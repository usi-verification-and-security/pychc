import logging
from pathlib import Path

import pytest
import functools

from pysmt.logics import LIA, QF_UFLIA
from pysmt.shortcuts import Int, Symbol, And, Plus, Equals, LT, FALSE, Not, Or
from pysmt.typing import INT, REAL, BOOL
from pysmt.environment import get_env
from pysmt.exceptions import PysmtTypeError

from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCInvalidResultException
from pychc.shortcuts import Predicate, Apply, Clause, Mod, IntDiv
from pychc.solvers.z3 import Z3CHCSolver, Z3SMTSolver
from pychc.solvers.witness import Status
from pychc.tests.common import reset_pysmt_env


@reset_pysmt_env
def test_mod_types():
    env = get_env()
    stc = env.stc
    r = Symbol("r", REAL)
    b = Symbol("b", BOOL)
    i = Symbol("i", INT)
    # TODO: check if this is intended
    stc.get_type(Mod(Int(2), Int(0)))
    stc.get_type(Mod(i, Int(0)))
    with pytest.raises(PysmtTypeError):
        stc.get_type(Mod(r, Int(2)))
    with pytest.raises(PysmtTypeError):
        stc.get_type(Mod(b, Int(2)))
    with pytest.raises(PysmtTypeError):
        stc.get_type(Mod(Int(2), b))
    # IntDiv mirrors Mod typing requirements
    stc.get_type(IntDiv(Int(2), Int(1)))
    with pytest.raises(PysmtTypeError):
        stc.get_type(IntDiv(r, Int(2)))
    with pytest.raises(PysmtTypeError):
        stc.get_type(IntDiv(b, Int(2)))
    with pytest.raises(PysmtTypeError):
        stc.get_type(IntDiv(Int(2), b))


def run_solver(test_func):
    @functools.wraps(test_func)
    def _wrapper(*args, **kwargs):
        sys = test_func(*args, **kwargs)
        assert isinstance(
            sys, CHCSystem
        ), "Test decorated with run_solver must return a CHCSystem"
        sys.serialize(Path("tmp.smt2"))

        sys1 = CHCSystem.load_from_smtlib(Path("tmp.smt2"))
        assert sys1.get_predicates() == sys.get_predicates()
        assert sys1.get_clauses() == sys.get_clauses()

        chc_solver = Z3CHCSolver(global_guidance=True)
        chc_solver.load_system(sys)
        validator = Z3SMTSolver(logic=LIA)
        chc_solver.set_smt_validator(validator)
        status = chc_solver.solve()
        assert status == Status.SAT
        chc_solver.validate_witness()

    return _wrapper


@reset_pysmt_env
@run_solver
def test_mod():
    sys = CHCSystem(logic=QF_UFLIA)
    inv = Predicate("inv", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv)
    sys.add_clause(Clause(head=Apply(inv, [Int(0)])))
    sys.add_clause(
        Clause(
            body=Apply(inv, [x]),
            head=Apply(inv, [Plus(x, Int(2))]),
        )
    )
    sys.add_clause(
        Clause(body=And(Apply(inv, [x]), Equals(Mod(x, Int(2)), Int(1))), head=FALSE())
    )
    return sys


@reset_pysmt_env
@run_solver
def test_mod2():
    sys = CHCSystem(logic=QF_UFLIA)
    inv = Predicate("inv", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv)
    sys.add_clause(Clause(head=Apply(inv, [Int(0)])))
    sys.add_clause(
        Clause(
            body=Apply(inv, [x]),
            head=Apply(inv, [Plus(x, Int(2))]),
        )
    )
    sys.add_clause(Clause(body=And(Apply(inv, [x]), Equals(x, Int(101))), head=FALSE()))

    return sys


@reset_pysmt_env
@run_solver
def test_intdiv():
    sys = CHCSystem(logic=QF_UFLIA)
    fail = Predicate("fail", [])
    x = Symbol("x", INT)
    x = Symbol("y", INT)
    sys.add_predicate(fail)
    sys.add_clause(Clause(body=fail, head=FALSE()))
    sys.add_clause(
        Clause(
            body=And(
                Equals(IntDiv(x, Int(2)), Int(0)),
                Not(Equals(x, Int(0))),
                Not(Equals(x, Int(1))),
            ),
            head=fail,
        )
    )
    return sys


SMTLIB_DIR = Path(__file__).parent / "smtlib"
SMTLIB_BENCHMARKS = list(SMTLIB_DIR.glob("*.smt2"))


@pytest.mark.parametrize("path", SMTLIB_BENCHMARKS, ids=str)
@reset_pysmt_env
@run_solver
def test_mod_smtlib_files(path: Path):
    if not path.exists():
        pytest.skip("No SMT-LIB mod benchmarks available yet")

    sys = CHCSystem.load_from_smtlib(path)
    return sys
