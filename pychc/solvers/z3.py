from __future__ import annotations

from typing import Optional

from pysmt.substituter import FunctionInterpretation
from pysmt.smtlib.parser.parser import SmtLibParser

from pychc.solvers.chc_witness import CHCStatus, CHCWitness, SatWitness
from pychc.solvers.chc_solver import CHCSolver, Options
from pychc.exceptions import PyCHCInvalidResultException


class Z3SmtLibParser(SmtLibParser):
    """Custom SMT-LIB parser for Z3 output."""

    def __init__(self, *args, predicates, **kwargs):
        super().__init__(*args, **kwargs)
        mgr = self.env.formula_manager

        def _mk_apply(pred):
            def _apply(*args):
                return mgr.Function(pred, list(args))

            return _apply

        self.interpreted.update(
            {
                pred.symbol_name(): self._operator_adapter(_mk_apply(pred))
                for pred in predicates
            }
        )


class Z3Options(Options):
    """Options passed to the Z3 process via command line flags."""

    def enable_print_witness(self, value: bool = True):
        """Enable certificate printing for fixedpoint: fp.print_certificate=true"""

        self._set_flag("fp.print_certificate=true", value)


class Z3Solver(CHCSolver):
    """Solver adapter for the Z3 CHC solver (fixedpoint)."""

    NAME = "z3"
    OPTION_CLASS = Z3Options

    def decide_result(self, output: str) -> CHCStatus:
        # certificate first and then status in last line
        last = output.splitlines()[-1].strip().lower() if output else ""
        if last == "sat":
            return CHCStatus.SAT
        if last == "unsat":
            return CHCStatus.UNSAT
        return CHCStatus.UNKNOWN

    def extract_model(self, output: str) -> Optional[SatWitness]:
        """
        Extract a SAT witness (model) from Z3 fixedpoint output.

        Parses equalities of the form `(= (pred args...) body)` and builds
        FunctionInterpretation entries for each predicate.
        """
        from io import StringIO

        predicates: dict[str, FunctionInterpretation] = {}

        lines = output.splitlines()
        if not lines:
            return None
        # Skip the last status line, add `(assert ...)` around the rest
        # this is a workaround to parse the output as SMT-LIB
        smt_text = "(assert " + "\n".join(lines[:-1]).strip() + ")"

        parser = Z3SmtLibParser(predicates=self.system.get_predicates())
        script = parser.get_script(StringIO(smt_text))

        annotations = script.annotations
        definitions = annotations.all_annotated_formulae("weight")
        for definition in definitions:
            if not definition.is_iff():
                continue
            lhs = definition.arg(0)
            rhs = definition.arg(1)
            if not lhs.is_function_application():
                continue
            pred_name = lhs.function_name()
            if pred_name not in self.system.get_predicates():
                raise PyCHCInvalidResultException(f"Unknown predicate {pred_name}")
            formal_params = lhs.args()
            interpretation = FunctionInterpretation(
                formal_params=formal_params,
                function_body=rhs,
                allow_free_vars=False,
            )
            predicates[pred_name.symbol_name()] = interpretation

        witness = SatWitness(predicates)
        if not self.system.check_witness_consistency(witness):
            raise PyCHCInvalidResultException(
                "Extracted model is not consistent with the CHC system predicates."
            )

        return witness

    def extract_unsat_proof(self, output: str) -> Optional[CHCWitness]:
        """Extract an UNSAT certificate/proof from solver output."""
        raise NotImplementedError
