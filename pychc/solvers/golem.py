"""
Golem instance of CHCSolver
"""

from __future__ import annotations

from enum import Enum
import logging

from typing import Optional

from pysmt.substituter import FunctionInterpretation
from pysmt.smtlib.parser.parser import SmtLibParser
from pysmt.typing import BOOL

from pychc.solvers.witness import ProofFormat, Status, SatWitness, UnsatWitness
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException


class GolemOptions(CHCSolverOptions):
    """Options passed to the Golem process via command line flags."""

    PROOF_FORMATS = {ProofFormat.LEGACY, ProofFormat.INTERMEDIATE, ProofFormat.ALETHE}

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        """Enable `--print-witness` to request witness output."""
        if proof_format:
            if proof_format not in self.PROOF_FORMATS:
                raise PyCHCSolverException(
                    f"Unsupported proof format for Golem: {proof_format}"
                )
            self._set_option(f"--proof-format", proof_format.value)
        self._set_flag("--print-witness", value)


class GolemSolver(CHCSolver):
    """Solver adapter for the Golem CHC solver."""

    NAME = "golem"
    OPTION_CLASS = GolemOptions

    def _decide_result(self):
        first = (
            self._raw_output.splitlines()[0].strip().lower() if self._raw_output else ""
        )
        if first == "sat":
            self._status = Status.SAT
        elif first == "unsat":
            self._status = Status.UNSAT
        else:
            self._status = Status.UNKNOWN

    def _extract_model(self) -> SatWitness:
        """
        Extract a SAT witness (model) from solver output.

        Assumes everything after the first line is SMT-LIB and may contain
        multiple `define-fun`. Stores each definition body as a pysmt formula.
        """
        from io import StringIO

        predicates: dict[str, FunctionInterpretation] = {}

        lines = self._raw_output.splitlines()
        if not lines:
            return None
        # Skip the first status line, first open and last closed parenthesis
        smt_text = "\n".join(lines[2:-1]).strip()

        parser = SmtLibParser()
        script = parser.get_script(StringIO(smt_text))
        decls = script.filter_by_command_name(("define-fun"))
        for decl in decls:
            args = getattr(decl, "args", [])
            if len(args) == 4:
                if args[2] != BOOL:
                    raise PyCHCInvalidResultException("Cannot parse: \n" + smt_text)
                name = args[0]
                params = args[1]
                body = args[3]
                if not params:
                    interpretation = body
                else:
                    interpretation = FunctionInterpretation(
                        formal_params=params, function_body=body, allow_free_vars=False
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

    def _extract_unsat_proof(self) -> UnsatWitness:
        """Extract an UNSAT certificate/proof from solver output."""

        lines = self._raw_output.splitlines()
        if not lines:
            return None
        # Skip the first status line
        smt_text = "\n".join(lines[1:]).strip()

        return UnsatWitness(smt_text, proof_format=self._proof_format)
