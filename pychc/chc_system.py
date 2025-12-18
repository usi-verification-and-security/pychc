from __future__ import annotations

import itertools
import logging

from pathlib import Path
from typing import Optional

from pysmt.shortcuts import ForAll
from pysmt.logics import Logic
from pysmt.fnode import FNode
from pysmt.smtlib.printers import SmtPrinter
from pysmt.typing import BOOL

from pychc.exceptions import PyCHCInvalidSystemException
from pychc.solvers.witness import SatWitness, UnsatWitness, Witness


class CHCSystem:
    def __init__(self, logic: Logic):
        self.logic: Logic = logic
        self.predicates: set[FNode] = set()
        self.clauses: set[FNode] = set()

    @classmethod
    def load_from_smtlib(cls, path: Path) -> CHCSystem:
        """Load a CHC system from an SMT-LIB file."""
        from pychc.parser import CHCSmtLibParser
        from pysmt.oracles import get_logic

        parser = CHCSmtLibParser()
        script = parser.get_script_fname(str(path))

        # helper
        get_content = lambda d: d.args[0]

        # collect declared predicates and asserted clauses
        predicates = set(
            map(get_content, script.filter_by_command_name(("declare-fun")))
        )
        clauses = list(map(get_content, script.filter_by_command_name("assert")))

        # determine logic
        logic = max(map(get_logic, clauses))

        # create system
        sys = cls(logic)
        [sys.add_predicate(pred) for pred in predicates]
        [sys.add_clause(clause) for clause in clauses]

        return sys

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
        is_fun = type_.is_function_type() and type_.return_type == BOOL
        if type_ != BOOL and not is_fun:
            raise PyCHCInvalidSystemException(
                f"Predicate {pred} {type_} must be a Boolean function."
            )
        if pred in self.predicates:
            raise PyCHCInvalidSystemException(f"Predicate {pred} already declared.")
        self.predicates.add(pred)

    def get_predicates(self) -> set[FNode]:
        return self.predicates

    def add_clause(self, clause: FNode) -> None:
        """
        Add a CHC clause.

        :param clause: a pysmt FNode representing a CHC clause.
        It must have no free variables and use a compliant logic.
        """
        from pysmt.oracles import get_logic

        is_function = lambda x: x.get_type().is_function_type()

        if clause.is_forall():
            open_clause = clause.arg(0)
        else:
            open_clause = clause
            # do not quantify function variables
            internal_vars = {
                v
                for v in open_clause.get_free_variables()
                if v not in self.predicates and not is_function(v)
            }
            clause = ForAll(internal_vars, open_clause)

        if set(clause.get_free_variables()) - self.predicates:
            logging.warning(
                f"Clause {clause} has free variables outside of declared predicates."
            )

        clause_logic = get_logic(open_clause)
        if not (clause_logic <= self.logic):
            raise PyCHCInvalidSystemException(
                f"Clause {clause} (of logic {clause_logic}) outside of system logic {self.logic}"
            )

        if not open_clause.is_implies():
            raise PyCHCInvalidSystemException(
                f"Clause {clause} must be an implication."
            )

        head = open_clause.arg(1)
        if len(self.predicates & head.get_free_variables()) > 1:
            raise PyCHCInvalidSystemException(
                f"Clause {clause} has multiple predicates in head."
            )
        self.clauses.add(clause)

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
            p: model.definitions[p.symbol_name()]
            for p in self.get_predicates()
            if p.get_type().is_function_type()
        }
        substitutions = {
            p: model.definitions[p.symbol_name()]
            for p in self.get_predicates()
            if not p.get_type().is_function_type()
        }

        def _substitute_clause(clause: FNode) -> FNode:
            if clause.is_forall():
                clause = clause.arg(0)
            return clause.substitute(
                subs=substitutions, interpretations=interpretations
            )

        return set(map(_substitute_clause, self.get_clauses()))

    def _check_sat_witness_consistency(self, witness: SatWitness) -> bool:
        """Check whether the given SAT witness is syntactically consistent."""
        from pysmt.substituter import FunctionInterpretation

        for pred in self.get_predicates():
            pred_name = pred.symbol_name()
            if pred_name not in witness.definitions:
                logging.error(f"Missing interpretation for predicate {pred_name}")
                return False
            interpretation = witness.definitions[pred_name]
            if isinstance(interpretation, FunctionInterpretation):
                ret_type = interpretation.function_body.get_type()
            else:
                ret_type = interpretation.get_type()
            if ret_type != BOOL:
                logging.error(f"Interpretation for {pred_name} is not Boolean")
                return False
            if pred.get_type().is_function_type():
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

    def check_witness_consistency(self, witness: Witness) -> bool:
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
                if pred.get_type().is_function_type():
                    args_str = " ".join(str(arg) for arg in pred.get_type().param_types)
                else:
                    args_str = " "
                f.write("(declare-fun ")
                printer.printer(pred)
                f.write(f" ({args_str}) Bool)\n")
            f.write("\n")
            for clause in self.clauses:
                f.write("(assert ")
                printer.printer(clause)
                f.write(")\n")
            f.write("(check-sat)\n")
        return out_path


# eoc CHCSystem
