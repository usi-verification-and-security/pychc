from __future__ import annotations

import itertools
import logging

from pathlib import Path
import tempfile
from typing import Optional

from pysmt.shortcuts import ForAll, And, Not, FALSE
from pysmt.logics import Logic
from pysmt.fnode import FNode
from pysmt.smtlib.printers import SmtPrinter
from pysmt.typing import BOOL

from pychc.exceptions import (
    PyCHCInvalidResultException,
    PyCHCInvalidSystemException,
)
from pychc.solvers import proof_checker
from pychc.solvers.smt_solver import SMTSolver
from pychc.solvers.witness import SatWitness, UnsatWitness, Witness, Status


class CHCSystem:
    def __init__(self, logic: Logic):
        self.logic: Logic = logic
        self.predicates: set[FNode] = set()
        self.clauses: list[FNode] = []
        self.smt2file: Optional[Path] = None

        self.status = None
        self.witness = None

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

        # do not set sys.smt2file.
        # sys.smt2file must be created with PySMT serializer
        # to remove comments and ensuring one last (check-sat)

        return sys

    def invalidate_data(self) -> None:
        if self.smt2file is not None:
            self.smt2file.unlink()
        self.smt2file = None
        self.status = None
        self.witness = None

    def get_logic(self) -> Optional[Logic]:
        return self.logic

    def add_predicate(self, pred: FNode) -> None:
        """
        Register a predicate symbol with its signature.

        :param pred: a pysmt Symbol of type FunctionType
        """
        self.invalidate_data()
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

    def add_clauses(self, clauses: set[FNode]) -> None:
        for clause in clauses:
            self.add_clause(clause)

    def add_clause(self, clause: FNode) -> int:
        """
        Add a CHC clause.

        :param clause: a pysmt FNode representing a CHC clause.
        It must have no free variables and use a compliant logic.
        """
        from pysmt.oracles import get_logic

        self.invalidate_data()

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

        if open_clause.is_implies():
            head = open_clause.arg(1)
            if len(self.predicates & head.get_free_variables()) > 1:
                raise PyCHCInvalidSystemException(
                    f"Clause {clause} has multiple predicates in head."
                )

        idx = len(self.clauses)
        self.clauses.append(clause)
        return idx

    def remove_clause(self, clause_idx: int) -> None:
        self.invalidate_data()
        del self.clauses[clause_idx]

    def get_clauses(self) -> list[FNode]:
        return self.clauses

    ## Witness syntactic consistency checks
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

    ## Witness semantic validation
    def _get_validate_model_queries(self, model: SatWitness) -> set[FNode]:
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

    def validate_sat_model(self, witness: SatWitness, smt_validator: SMTSolver):
        from pysmt.oracles import get_logic

        if not smt_validator.get_logic():
            smt_validator.set_logic(self.get_logic())

        queries = self._get_validate_model_queries(witness)
        for query in queries:
            query_logic = get_logic(query)
            known_logic = query_logic <= smt_validator.get_logic()
            if not known_logic and query_logic.is_quantified():
                # attempt to eliminate quantifiers
                try:
                    from pysmt.shortcuts import QuantifierEliminator

                    logging.warning(
                        "Performing quantifier elimination for witness validation."
                    )
                    qe = QuantifierEliminator(name="z3")
                    query = qe.eliminate_quantifiers(query)
                except Exception as e:
                    logging.warning(
                        "Quantifier elimination failed, cannot validate witness."
                    )

            if not smt_validator.is_valid(query):
                raise PyCHCInvalidResultException(
                    f"Solver {smt_validator.NAME} produced an invalid model for the system. See satisfiable query: {smt_validator.get_smt2_file()}"
                )
            if smt_validator.proof_checker:
                smt_validator.validate_proof()
            # else:
            #     logging.warning(
            #         f"No proof checker set for SMT solver {smt_validator.NAME}, skipping proof validation"
            #     )
        self.status = Status.SAT
        self.witness = witness

    def validate_unsat_proof(
        self, witness: UnsatWitness, proof_checker: proof_checker.ProofChecker, use_smt2file: Optional[Path]=None
    ):
        if use_smt2file:
            smt2file = use_smt2file
        else:
            smt2file = self.get_smt2file()
        proof_file = Path(tempfile.NamedTemporaryFile("w", suffix=".proof").name)
        with open(proof_file, "w") as pf:
            pf.write(witness.text)

        ok = proof_checker.validate(proof_file=proof_file, smt2file=smt2file)
        if not ok:
            raise PyCHCInvalidResultException(
                f"Proof checker {proof_checker.NAME} failed to validate the proof {proof_file} on {smt2file}."
            )
        # if everything went fine, delete temp file
        proof_file.unlink()
        self.status = Status.UNSAT
        self.witness = witness

    def learn_from_witness(self, witness: Witness) -> set[FNode]:
        """
        Learn new clauses from the given witness.

        :param witness: a Witness containing the interpretations for the predicates
        """
        from pychc.shortcuts import Clause, Apply
        from pysmt.oracles import get_logic

        if not isinstance(witness, SatWitness):
            logging.warning("Can only learn from SAT witnesses.")
            return set()

        clauses = set()
        for pred in self.get_predicates():
            interpretation = witness.definitions.get(pred.symbol_name(), None)
            if pred.get_type().is_function_type():
                predicate = Apply(pred, interpretation.formal_params)
                property = interpretation.function_body
            else:
                predicate = pred
                property = interpretation

            body = And(predicate, Not(property))
            if not get_logic(body) <= self.logic:
                logging.warning(
                    f"Learned clause body {body} logic not compatible with system logic."
                )
                # TODO: Could try to remove quantifiers here.
                continue
            clauses.add(Clause(body=body, head=FALSE()))

        for clause in clauses:
            self.add_clause(clause)
        return clauses

    def get_smt2file(self) -> Path:
        if self.smt2file is None or not self.smt2file.exists():
            self.smt2file = Path(
                tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False).name
            )
            self.serialize(self.smt2file)
        return self.smt2file

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
        self.smt2file = out_path
        return out_path


# eoc CHCSystem
