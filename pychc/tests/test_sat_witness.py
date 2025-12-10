import pytest
import functools

from pysmt.logics import QF_UFLIA, QF_UFLRA
from pysmt.shortcuts import (
    Int,
    Real,
    Symbol,
    And,
    Equals,
    Plus,
    LT,
    TRUE,
    FALSE,
    Minus,
    Solver,
)
from pysmt.typing import INT, REAL

from pychc.chc_system import CHCSystem
from pychc.shortcuts import Predicate, Apply
from pychc.exceptions import PyCHCInvalidResultException

from pychc.tests.common import reset_pysmt_env


def run_solver(test_func):
    @functools.wraps(test_func)
    def _wrapper(*args, **kwargs):
        from pychc.chc_system import CHCSystem

        sys = test_func(*args, **kwargs)
        assert isinstance(
            sys, CHCSystem
        ), "Test decorated with run_chc_solver must return a CHCSystem"

        from pathlib import Path

        sys.serialize(Path("tmp.smt2"))

        from pychc.solvers.golem import GolemSolver
        from pychc.solvers.z3 import Z3Solver

        validator = Solver(name="z3")
        for CHCSolverClass in (GolemSolver, Z3Solver):
            solver = CHCSolverClass(sys)
            solver.solve(get_witness=True)
            model = solver.get_witness()
            queries = sys.get_validate_model_queries(model)
            assert queries
            for query in queries:
                if not validator.is_valid(query):
                    raise PyCHCInvalidResultException(
                        f"Solver {CHCSolverClass.NAME} produced an invalid model for the system."
                    )

    return _wrapper


@reset_pysmt_env
@run_solver
def test_system1():
    sys = CHCSystem(logic=QF_UFLIA)
    inv = Predicate("inv", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv)
    sys.add_clause(head=Apply(inv, [Int(0)]))
    sys.add_clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))]))
    sys.add_clause(body=And(Apply(inv, [x]), LT(x, Int(0))), head=FALSE())
    return sys


@reset_pysmt_env
@run_solver
def test_system2():
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
