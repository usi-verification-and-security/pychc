import pytest
from pathlib import Path
import functools, logging

from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import (
    Int,
    Symbol,
    And,
    Plus,
    LT,
    FALSE,
    Minus,
)
from pysmt.typing import INT, REAL
from pysmt.oracles import get_logic

from pychc.chc_system import CHCSystem
from pychc.shortcuts import Predicate, Apply
from pychc.exceptions import PyCHCSolverException

from pychc.solvers.witness import ProofFormat, Status
from pychc.tests.common import reset_pysmt_env

from pychc.solvers.golem import GolemSolver

ALL_OPTIONS = [
    (GolemSolver, ProofFormat.ALETHE, True),
    (GolemSolver, ProofFormat.LEGACY, True),
    (GolemSolver, ProofFormat.INTERMEDIATE, True),
    (GolemSolver, ProofFormat.DOT, False),
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
        proof = kwargs.pop("proof", None)
        expected_ok = kwargs.pop("expected_ok", True)

        # Run CHC solver
        chc_solver = chc_cls()
        chc_solver.load_system(sys)

        if not expected_ok:
            with pytest.raises(PyCHCSolverException):
                chc_solver.solve(get_witness=True, proof_format=proof)
            return
    
        status = chc_solver.solve(get_witness=True, proof_format=proof)
        assert status == Status.UNSAT, "Expected UNSAT result from the solver"
        model = chc_solver.get_witness()
        assert model is not None, "Expected a witness/model from the solver"

    return _wrapper


@pytest.mark.parametrize(
    "chc_class,proof,expected_ok",
    ALL_OPTIONS,
)
@reset_pysmt_env
@run_solver
def test_system1(chc_class, proof, expected_ok):
    sys = CHCSystem(logic=QF_UFLIA)
    inv = Predicate("inv", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv)
    sys.add_clause(head=Apply(inv, [Int(0)]))
    sys.add_clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))]))
    sys.add_clause(body=And(Apply(inv, [x]), LT(x, Int(5))), head=FALSE())
    return sys


@pytest.mark.parametrize(
    "chc_class,proof,expected_ok",
    ALL_OPTIONS,
)
@reset_pysmt_env
@run_solver
def test_system2(chc_class, proof, expected_ok):
    sys = CHCSystem(logic=QF_UFLIA)
    inv1 = Predicate("inv1", [INT])
    inv2 = Predicate("inv2", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv1)
    sys.add_predicate(inv2)
    sys.add_clause(head=Apply(inv1, [Int(0)]))
    sys.add_clause(body=Apply(inv1, [x]), head=Apply(inv1, [Plus(x, Int(1))]))
    sys.add_clause(body=Apply(inv1, [x]), head=Apply(inv2, [Minus(Int(0), x)]))
    sys.add_clause(body=And(Apply(inv2, [x]), LT(Int(-5), x)), head=FALSE())
    return sys
