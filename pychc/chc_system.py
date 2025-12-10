from __future__ import annotations

import itertools
import logging

from pathlib import Path
from typing import Optional

from pysmt.logics import Logic
from pysmt.fnode import FNode
from pysmt.smtlib.printers import SmtPrinter
from pysmt.typing import BOOL

from pychc.exceptions import PyCHCInvalidSystemException
from pychc.solvers.chc_witness import SatWitness, UnsatWitness, CHCWitness


class CHCSystem:
    def __init__(self, logic: Logic):
        self.logic: Logic = logic
        self.predicates: set[FNode] = set()
        self.clauses: set[FNode] = set()

        self._is_linear: bool = True

    def get_logic(self) -> Optional[Logic]:
        return self.logic

    def add_predicate(self, pred: FNode) -> None:
        """
        Register a predicate symbol with its signature.

        :param pred: a pysmt Symbol of type FunctionType
        """
        try:
            type_ = pred.get_type()
        except Exception as e:
            raise PyCHCInvalidSystemException(
                f"Error getting type of predicate {pred}: {e}"
            ) from e
        if not type_.is_function_type():
            raise PyCHCInvalidSystemException(
                f"Predicate {pred} must have a function type."
            )
        if type_.return_type != BOOL:
            raise PyCHCInvalidSystemException(
                f"Predicate {pred} must have Boolean return type."
            )
        if pred in self.predicates:
            raise PyCHCInvalidSystemException(f"Predicate {pred} already declared.")
        self.predicates.add(pred)

    def get_predicates(self) -> set[FNode]:
        return self.predicates

    def add_clause(self, head: FNode, body: Optional[FNode] = None) -> None:
        """
        Add a CHC clause.

        :param formula: a pysmt FNode representing a CHC clause.
        It must have no free variables and use a compliant logic.
        """
        from pysmt.oracles import get_logic
        from pysmt.shortcuts import Implies, ForAll, TRUE

        clause = head if body is None else Implies(body, head)
        clause_logic = get_logic(clause)
        if not (clause_logic <= self.logic):
            raise PyCHCInvalidSystemException(
                f"Clause {clause} (of logic {clause_logic}) outside of system logic {self.logic}"
            )
        if clause_logic.is_quantified():
            raise PyCHCInvalidSystemException(
                f"Clause {clause} should not be quantified."
            )
        head_preds = list(
            filter(lambda x: x.is_function_application(), head.get_atoms())
        )
        if len(head_preds) > 1:
            raise PyCHCInvalidSystemException(
                f"Head {head} must be a single predicate."
            )
        body = body if body is not None else TRUE()
        body_preds = set(
            filter(lambda x: x.is_function_application(), body.get_atoms())
        )
        if len(body_preds) > 1:
            self._is_linear = False
        for pred in set(head_preds) | body_preds:
            if pred.function_name() not in self.predicates:
                raise PyCHCInvalidSystemException(
                    f"Predicate {pred.arg(0)} used in clause {clause} not declared."
                )

        fv = clause.get_free_variables() - self.predicates
        closed_clause = clause if len(fv) == 0 else ForAll(fv, clause)
        self.clauses.add(closed_clause)

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
            # collect the predicates appearing in clauses
            # an used predicate is clause free variable mentioned in self.predicates.
            used_preds = set(
                itertools.chain.from_iterable(
                    self.predicates & clause.get_free_variables()
                    for clause in self.clauses
                )
            )
            for pred in used_preds:
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
