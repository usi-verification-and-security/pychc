from __future__ import annotations

import functools
from pathlib import Path
from typing import Optional

from pysmt.logics import QF_LRA, QF_LIA, Logic
from pysmt.substituter import FunctionInterpretation
from pysmt.smtlib.parser.parser import SmtLibParser
from pysmt.fnode import FNode

from pychc.parser import CHCSmtLibParser
from pychc.solvers.witness import ProofFormat, Status, UnsatWitness, SatWitness
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException


class Z3CHCOptions(CHCSolverOptions):
    """Options passed to the Z3 process via command line flags."""

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        """Enable certificate printing for fixedpoint: fp.print_certificate=true"""
        if proof_format:
            raise PyCHCSolverException(f"Z3 only supports its native proof format.")
        self._set_flag("fp.print_certificate=true", value)


class Z3CHCSolver(CHCSolver):
    """Solver adapter for the Z3 CHC solver."""

    NAME = "z3"
    OPTION_CLASS = Z3CHCOptions

    def _decide_result(self):
        # certificate first and then status in last line
        last = (
            self._raw_output.splitlines()[-1].strip().lower()
            if self._raw_output
            else ""
        )
        if last == "sat":
            self._status = Status.SAT
        elif last == "unsat":
            self._status = Status.UNSAT
        else:
            self._status = Status.UNKNOWN

    def _extract_model(self) -> SatWitness:
        """
        Extract a SAT witness (model) from Z3 fixedpoint output.

        Parses equalities of the form `(= (pred args...) body)` and builds
        FunctionInterpretation entries for each predicate.
        """
        import itertools
        from copy import copy
        from io import StringIO
        from pysmt.rewritings import conjunctive_partition

        predicates: dict[str, FunctionInterpretation] = {}

        lines = self._raw_output.splitlines()
        if not lines:
            return None
        # Skip the last status line, add `(assert ...)` around the rest
        # this is a workaround to parse the output as SMT-LIB
        smt_text = "\n(assert " + "\n".join(lines[:-1]).strip() + ")"

        parser = CHCSmtLibParser(predicates=copy(self.system.get_predicates()))
        script = parser.get_script(StringIO(smt_text))

        candidates = itertools.chain(
            script.annotations.all_annotated_formulae("weight"),
            conjunctive_partition(script.get_last_formula()),
        )
        for iff in filter(lambda x: x.is_iff(), candidates):
            lhs, rhs = iff.args()
            if not lhs.is_function_application():
                if lhs not in self.system.get_predicates():
                    continue
                predicates[lhs.symbol_name()] = rhs
            else:
                pred_symbol = lhs.function_name()
                if pred_symbol not in self.system.get_predicates():
                    continue
                formal_params = lhs.args()
                interpretation = FunctionInterpretation(
                    formal_params=formal_params,
                    function_body=rhs,
                    allow_free_vars=False,
                )
                predicates[pred_symbol.symbol_name()] = interpretation

        witness = SatWitness(predicates)
        if not self.system.check_witness_consistency(witness):
            raise PyCHCInvalidResultException(
                "Extracted model is not consistent with the CHC system predicates."
            )

        return witness

    def _extract_unsat_proof(self) -> UnsatWitness:
        """Extract an UNSAT certificate/proof from solver output."""
        raise NotImplementedError


class Z3SMTOptions(SMTSolverOptions):
    """
    Options for Z3 SMT solver.
    """

    PROOF_FORMATS = set()

    def __init__(self, proof_format: Optional[ProofFormat] = None, **base_options):
        super().__init__(**base_options)
        if proof_format:
            raise ValueError(f"Z3 only supports its native proof format.")


class Z3SMTSolver(SMTSolver):
    """Z3 SMT solver adapter using SMT-LIB textual interface."""

    NAME = "z3"
    LOGICS = (QF_LRA, QF_LIA)
    OptionsClass = Z3SMTOptions

    def __init__(
        self,
        logic: Logic,
        binary_path: Optional[Path] = None,
        **options,
    ):
        super().__init__(
            logic=logic, binary_path=binary_path, cmd_args=["-in"], **options
        )
