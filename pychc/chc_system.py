from __future__ import annotations

import logging

from pathlib import Path
from typing import Optional

from pysmt.logics import Logic
from pysmt.fnode import FNode
from pysmt.smtlib.printers import SmtPrinter
from pysmt.typing import BOOL

from pychc.solvers.chc_witness import SatWitness, UnsatWitness, CHCWitness


class CHCSystem:
    def __init__(self):
        self.logic: Logic = None
        self.predicates: set[FNode] = set()
        self.clauses: set[FNode] = set()

    def set_logic(self, logic: Logic) -> None:
        self.logic = logic

    def get_logic(self) -> Optional[Logic]:
        return self.logic

    def add_predicate(self, pred: FNode) -> None:
        """
        Register a predicate symbol with its signature.

        :param pred: a pysmt Symbol of type FunctionType
        """
        # TODO: check type
        self.predicates.add(pred)

    def get_predicates(self) -> set[FNode]:
        return self.predicates

    def add_clause(self, formula: FNode) -> None:
        """
        Add a CHC clause.

        :param formula: a pysmt FNode representing a CHC clause.
        It must have no free variables and use a compliant logic.
        """
        # TODO: check logic compliance, predicate usage, etc.
        self.clauses.add(formula)

    def get_clauses(self) -> set[FNode]:
        return self.clauses

    def get_validate_model_queries(self, model: SatWitness) -> set[FNode]:
        """
        Given a SAT witness/model, produce the set of queries to validate it.

        :param model: a SatWitness containing the interpretations for the predicates
        :return: a set of FNodes representing the queries to validate the model.

        Each query corresponds to a clause in the system, with predicates
        replaced by their definitions in the model.
        The model is validated if all queries are valid formulae.
        """
        assert self.check_witness_consistency(
            model
        ), "Given model is not consistent with the CHC system predicates."

        interpretations = {
            p: model.definitions[p.symbol_name()] for p in self.get_predicates()
        }

        def _substitute_clause(clause: FNode) -> FNode:
            if clause.is_forall():
                clause = clause.arg(0)
            return clause.substitute(subs={}, interpretations=interpretations)

        return set(map(_substitute_clause, self.get_clauses()))

    def _check_sat_witness_consistency(self, witness: SatWitness) -> bool:
        """Check whether the given SAT witness is syntactically consistent."""
        for pred in self.get_predicates():
            pred_name = pred.symbol_name()
            if pred_name not in witness.definitions:
                logging.error(f"Missing interpretation for predicate {pred_name}")
                return False
            interpretation = witness.definitions[pred_name]
            if interpretation.function_body.get_type() != BOOL:
                logging.error(f"Interpretation for {pred_name} is not Boolean")
                return False
            pred_arg_types = pred.get_type().param_types
            if len(interpretation.formal_params) != len(pred_arg_types):
                logging.error(f"Mismatch in number of parameters for {pred_name}")
                return False
            for i, param in enumerate(interpretation.formal_params):
                if param.get_type() != pred.get_type().param_types[i]:
                    logging.error(f"Type mismatch for parameter {i} of {pred_name}")
                    return False
        return True

    def _check_unsat_witness_consistency(self, witness: UnsatWitness) -> bool:
        """Check whether the given UNSAT witness is syntactically consistent."""
        raise NotImplementedError()

    def check_witness_consistency(self, witness: CHCWitness) -> bool:
        """
        Check whether the given witness is *syntactically* consistent with the system.

        :param witness: a Witness containing the interpretations for the predicates

        """
        if isinstance(witness, SatWitness):
            return self._check_sat_witness_consistency(witness)
        if isinstance(witness, UnsatWitness):
            return self._check_unsat_witness_consistency(witness)
        return True

    def serialize(self, out_path: Path) -> Path:
        """
        Serialize the system to SMT-LIB at `out_path`.

        Emits:
        - `(set-logic HORN)`
        - `(declare-fun <pred> (<arg_sorts> ) <return_sort>)` for each predicate
        - `(assert <clause>)` for each clause
        - `(check-sat)` at the end

        :return: the Path where the system was written
        """
        with out_path.open("w") as f:
            printer = SmtPrinter(f)
            f.write(f"(set-logic HORN)\n")
            for pred in self.predicates:
                args_str = " ".join(str(arg) for arg in pred.get_type().param_types)
                f.write(f"(declare-fun {pred.symbol_name()} ({args_str}) Bool)\n")
            f.write("\n")
            for clause in self.clauses:
                f.write("(assert ")
                printer.printer(clause)
                f.write(")\n")
            f.write("(check-sat)\n")
        return out_path


# eoc CHCSystem
