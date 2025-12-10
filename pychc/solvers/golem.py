"""
Golem instance of CHCSolver
"""

from __future__ import annotations

import logging

from typing import Optional

from pysmt.substituter import FunctionInterpretation
from pysmt.smtlib.parser.parser import SmtLibParser
from pysmt.typing import BOOL

from pychc.solvers.chc_witness import CHCStatus, SatWitness
from pychc.solvers.chc_solver import CHCSolver, Options
from pychc.exceptions import PyCHCInvalidResultException


class GolemOptions(Options):
    """Options passed to the Golem process via command line flags."""

    def enable_print_witness(self, value: bool = True):
        """Enable `--print-witness` to request witness output."""

        self._set_flag("--print-witness", value)


class GolemSolver(CHCSolver):
    """Solver adapter for the Golem CHC solver."""

    NAME = "golem"
    OPTION_CLASS = GolemOptions

    def decide_result(self, output: str) -> CHCStatus:
        first = output.splitlines()[0].strip().lower() if output else ""
        if first == "sat":
            return CHCStatus.SAT
        if first == "unsat":
            return CHCStatus.UNSAT
        return CHCStatus.UNKNOWN

    def extract_model(self, output: str) -> Optional[SatWitness]:
        """
        Extract a SAT witness (model) from solver output.

        Assumes everything after the first line is SMT-LIB and may contain
        multiple `define-fun`. Stores each definition body as a pysmt formula.
        """
        from io import StringIO

        predicates: dict[str, FunctionInterpretation] = {}

        lines = output.splitlines()
        if not lines:
            return None
        # Skip the first status line, first open and last closed parenthesis
        smt_text = "\n".join(lines[2:-1]).strip()

        parser = SmtLibParser()
        script = parser.get_script(StringIO(smt_text))
        decls = script.filter_by_command_name(("declare-fun", "define-fun"))
        for decl in decls:
            args = getattr(decl, "args", [])
            if len(args) == 4:
                if args[2] != BOOL:
                    raise PyCHCInvalidResultException("Cannot parse: \n" + smt_text)
                name = args[0]
                interpretation = FunctionInterpretation(
                    formal_params=args[1], function_body=args[3], allow_free_vars=False
                )
                predicates[name] = interpretation
            else:
                logging.warning(f"Skipping malformed declaration? {decl}")

        witness = SatWitness(predicates)
        if not self.system.check_witness_consistency(witness):
            raise PyCHCInvalidResultException(
                "Extracted model is not consistent with the CHC system predicates."
            )

        return witness

    def extract_unsat_proof(self, output: str) -> Optional[UnsatWitness]:
        """Extract an UNSAT certificate/proof from solver output."""

        raise NotImplementedError
