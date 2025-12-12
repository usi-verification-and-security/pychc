import pytest
from pathlib import Path
import functools, logging

from pysmt.logics import QF_UFLIA, QF_UFLRA
from pysmt.shortcuts import (
    Int,
    Symbol,
    And,
    Plus,
    LT,
    FALSE,
    Minus,
    QuantifierEliminator,
)
from pysmt.typing import INT, REAL
from pysmt.oracles import get_logic

from pychc.chc_system import CHCSystem
from pychc.shortcuts import Predicate, Apply
from pychc.exceptions import PyCHCInvalidResultException

from pychc.tests.common import reset_pysmt_env

from pychc.solvers.golem import GolemSolver
from pychc.solvers.z3 import Z3Solver

from pychc.solvers.opensmt import OpenSMTSolver
from pychc.solvers.cvc5 import CVC5Solver, ProofFormat

ALL_OPTIONS = [
    (GolemSolver, OpenSMTSolver, None),
    (GolemSolver, CVC5Solver, {"proof_format": ProofFormat.ALETHE}),
    (GolemSolver, CVC5Solver, {"proof_format": ProofFormat.LFSC}),
    (GolemSolver, CVC5Solver, {"proof_format": ProofFormat.DOT}),
    (Z3Solver, OpenSMTSolver, None),
    (Z3Solver, CVC5Solver, {"proof_format": ProofFormat.ALETHE}),
    (Z3Solver, CVC5Solver, {"proof_format": ProofFormat.LFSC}),
    (Z3Solver, CVC5Solver, {"proof_format": ProofFormat.DOT}),
]


def run_solver(test_func):
    @functools.wraps(test_func)
    def _wrapper(*args, **kwargs):
        sys = test_func(*args, **kwargs)
        assert isinstance(
            sys, CHCSystem
        ), "Test decorated with run_solver must return a CHCSystem"
        # Serialize for debugging/reference
        sys.serialize(Path("tmp.smt2"))

        chc_cls = kwargs.pop("chc_class", None)
        smt_cls = kwargs.pop("smt_class", None)
        smt_kw = kwargs.pop("smt_kwargs", None) or {}

        # Run CHC solver
        chc_solver = chc_cls(sys)
        chc_solver.solve(get_witness=True)
        model = chc_solver.get_witness()

        # Instantiate SMT validator
        validator = smt_cls(logic=sys.get_logic(), **smt_kw)

        # Z3 might return quantified interpretations for the predicates
        # TODO: check if performing QE with z3 is ok for the certification purposes
        qe = QuantifierEliminator(name="z3")

        # Validate model
        queries = sys.get_validate_model_queries(model)
        assert queries
        for query in queries:
            logging.info(query.serialize())
            query_logic = get_logic(query)
            if query_logic.is_quantified():
                query = qe.eliminate_quantifiers(query)
                logging.warning("Removed quantifiers from query")

            if not validator.is_valid(query):
                raise PyCHCInvalidResultException(
                    f"Solver {chc_cls.NAME} produced an invalid model for the system."
                )
            proof = validator.get_proof()
            if not proof:
                raise PyCHCInvalidResultException(
                    f"Solver {smt_cls.NAME} produces a null proof."
                )

    return _wrapper


@pytest.mark.parametrize(
    "chc_class,smt_class,smt_kwargs",
    ALL_OPTIONS,
)
@reset_pysmt_env
@run_solver
def test_system1(chc_class, smt_class, smt_kwargs):
    sys = CHCSystem(logic=QF_UFLIA)
    inv = Predicate("inv", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv)
    sys.add_clause(head=Apply(inv, [Int(0)]))
    sys.add_clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))]))
    sys.add_clause(body=And(Apply(inv, [x]), LT(x, Int(0))), head=FALSE())
    return sys


@pytest.mark.parametrize(
    "chc_class,smt_class,smt_kwargs",
    ALL_OPTIONS,
)
@reset_pysmt_env
@run_solver
def test_system2(chc_class, smt_class, smt_kwargs):
    sys = CHCSystem(logic=QF_UFLIA)
    inv1 = Predicate("inv1", [INT])
    inv2 = Predicate("inv2", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv1)
    sys.add_predicate(inv2)
    sys.add_clause(head=Apply(inv1, [Int(0)]))
    sys.add_clause(body=Apply(inv1, [x]), head=Apply(inv1, [Plus(x, Int(1))]))
    sys.add_clause(body=Apply(inv1, [x]), head=Apply(inv2, [Minus(Int(0), x)]))
    sys.add_clause(body=And(Apply(inv2, [x]), LT(Int(0), x)), head=FALSE())
    return sys
