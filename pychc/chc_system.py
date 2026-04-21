#
# Copyright 2026 Anna Becchi
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from __future__ import annotations

import itertools
import logging

from pathlib import Path
import tempfile
from typing import Optional

from pysmt.shortcuts import ForAll, And
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
    def load_from_file(cls, path: Path, logic: Optional[Logic] = None) -> CHCSystem:
        """
        Load a CHC system from an SMT-LIB file.

        :param path: path to the SMT-LIB file containing the CHC system.
        :param logic: (optional) logic of the system. If None, it will be inferred from the clauses.
        :return: a CHCSystem instance representing the system in the file.
        """
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
        def get_clause_logic(clause):
            if clause.is_forall():
                return get_logic(clause.arg(0))
            return get_logic(clause)

        if logic is None:
            logic = max(map(get_clause_logic, clauses))

        # create system
        sys = cls(logic)
        for pred in predicates: sys.add_predicate(pred)
        for clause in clauses: sys.add_clause(clause)

        # Although `path` is a valid SMT-LIB file containing the system,
        # do not cache it as the `sys.smt2file`.
        # `sys.smt2file` must be created with PySMT serializer
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
        This invalidates the current solving status, witness, and SMT-LIB file, if any.

        :param pred: a pysmt Symbol of type FunctionType, or a Boolean variable
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
        Add a new CHC clause and returns its index.
        This invalidates the current solving status, witness, and SMT-LIB file, if any.

        :param clause: a pysmt FNode representing a CHC clause.
            All free variables that are not declared predicates will be universally quantified.
        :return: the index of the added clause in the system.
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
        """
        Remove the clause with the given index.
        This invalidates the current solving status, witness, and SMT-LIB file, if any.

        :param clause_idx: the index of the clause to remove. It must be <= len(get_clauses()).
        """
        self.invalidate_data()
        del self.clauses[clause_idx]

    def get_clauses(self) -> list[FNode]:
        """
        Get the list of clauses in the system.

        :return: a list of FNodes representing the clauses in the system.
        """
        return self.clauses

    ## Witness syntactic consistency checks
    def _check_sat_witness_consistency(self, witness: SatWitness) -> bool:
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
    def _get_validate_model_queries(self, model: SatWitness) -> list[FNode]:
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

        return list(map(_substitute_clause, self.get_clauses()))

    def validate_sat_model(
        self,
        witness: SatWitness,
        smt_validator: SMTSolver,
        timeout: Optional[int] = None,
    ):
        """
        Validate a SAT witness by checking that it satisfies all clauses in the system.
        A PyCHCInvalidResultException is raised if the witness is invalid.

        :param witness: a SatWitness containing the interpretations for the predicates
        :param smt_validator: an SMT solver to use for validating the witness
        :param timeout: (optional) timeout in seconds for the SMT solver during validation
        """
        from pysmt.oracles import get_logic

        queries = self._get_validate_model_queries(witness)

        # Set the smt_validator logic, if not already set.
        logic = max(map(get_logic, queries))
        if not smt_validator.get_logic():
            if any(logic <= l for l in smt_validator.LOGICS):
                smt_validator.set_logic(logic)
            else:
                # If smt_validator does not support the logic of the queries,
                # try to set the system's logic. It might be due to quantifiers in the witness,
                # which will be removed later.
                smt_validator.set_logic(self.get_logic())

        smt_validator.set_timeout(timeout)

        for i, query in enumerate(queries):
            query_logic = get_logic(query)
            known_logic = query_logic <= smt_validator.get_logic()

            # If the smt_validator does not support the logic of the query, try to remove quantifiers.
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
                    # TODO: raise a specific exception for quantifier elimination failure?
                    logging.warning(
                        "Quantifier elimination failed, cannot validate witness."
                    )

            # perform actual validation of the query
            if not smt_validator.is_valid(query):
                logging.error(f"Falsified clause: {self.get_clauses()[i].serialize(threshold=6)}")
                logging.error(f"Interpreted clause is not valid: {query.serialize(threshold=6)}")
                raise PyCHCInvalidResultException(
                    f"Invalid CHC model. Clause {i} is falsified. See satisfiable query: {smt_validator.get_smt2_file()}"
                )
            # if the smt_validator supports proof checking, validate the proof as well
            if smt_validator.proof_checker:
                smt_validator.validate_proof()

        # Here, no invalidity was found.
        self.status = Status.SAT
        self.witness = witness

    def validate_unsat_proof(
        self,
        witness: UnsatWitness,
        proof_checker: proof_checker.ProofChecker,
        timeout: Optional[int] = None,
    ):
        """
        Validate an UNSAT witness by checking the proof using the provided proof checker.
        A PyCHCInvalidResultException is raised if the proof is invalid.

        :param witness: an UnsatWitness containing the proof for the UNSAT result
        :param proof_checker: a ProofChecker to use for validating the proof
        :param timeout: (optional) timeout in seconds for the proof checker during validation
        """
        smt2file = self.get_smt2file()
        proof_checker.validate_witness(witness, smt2file, timeout=timeout)
        self.status = Status.UNSAT
        self.witness = witness

    def strengthen_clause_with_witness(
        self, clause_id: int, witness: SatWitness
    ) -> int:
        """
        Learn new clauses from the given witness.

        :param clause_id: the index of the clause to strengthen. It must be <= len(get_clauses()).
          If the clause is not a quantified implication (eg, it is a fact), this has no effect
          and `clause_id` is returned.
        :param witness: a Witness containing the interpretations for the predicates
        :return: the index of the (possibly new) clause in the system.
        """
        from pychc.shortcuts import Clause

        clause = self.clauses[clause_id]

        if not clause.is_forall() or not clause.arg(0).is_implies():
            logging.info("Can only strengthen quantified implication clauses.")
            return clause_id

        # prepare maps for interpreting a formula
        interpretations = {
            p: witness.definitions[p.symbol_name()]
            for p in self.get_predicates()
            if p.get_type().is_function_type()
        }
        substitutions = {
            p: witness.definitions[p.symbol_name()]
            for p in self.get_predicates()
            if not p.get_type().is_function_type()
        }

        body, head = clause.arg(0).args()
        interpreted_body = body.substitute(
            subs=substitutions, interpretations=interpretations
        )
        interpreted_head = head.substitute(
            subs=substitutions, interpretations=interpretations
        )
        new_body = And(body, interpreted_body, interpreted_head)
        new_clause_id = self.add_clause(Clause(body=new_body, head=head))
        return new_clause_id

    def get_smt2file(self) -> Path:
        """ 
        Get the cached path to the SMT-LIB file representing the system.
        If the file does not exist yet, it is created by serializing the system to it.
        """
        if self.smt2file is None or not self.smt2file.exists():
            self.smt2file = Path(
                tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False).name
            )
            self.serialize(self.smt2file)
        return self.smt2file

    def serialize(self, out_path: Path) -> Path:
        """
        Serialize the system to SMT-LIB.
        Emits:
        - `(set-logic HORN)`
        - `(declare-fun <pred> (<arg_sorts> ) <return_sort>)` for each predicate
        - `(assert <clause>)` for each clause
        - `(check-sat)` at the end

        :param out_path: the Path where to write the SMT-LIB file
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

