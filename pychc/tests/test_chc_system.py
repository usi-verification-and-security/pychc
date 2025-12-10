import pytest
import functools

from pysmt.logics import QF_UFLIA, QF_UFLRA
from pysmt.shortcuts import Int, Real, Symbol, And, Equals, Plus, LT, TRUE, FALSE
from pysmt.typing import INT, REAL, BOOL, FunctionType

from pychc.chc_system import CHCSystem
from pychc.shortcuts import Predicate, Apply
from pychc.exceptions import PyCHCInvalidSystemException


def run_chc_solver(test_func):
    @functools.wraps(test_func)
    def _wrapper(*args, **kwargs):
        from pychc.chc_system import CHCSystem

        sys = test_func(*args, **kwargs)
        assert isinstance(
            sys, CHCSystem
        ), "Test decorated with run_chc_solver must return a CHCSystem"

        for clause in sys.get_clauses():
            assert not clause.is_quantifier() or clause.is_forall()
            assert clause.get_free_variables().issubset(sys.get_predicates())

        from pychc.solvers.golem import GolemSolver

        solver = GolemSolver(sys)
        solver.solve(get_witness=False)

    return _wrapper


def reset_pysmt_env(test_func):
    @functools.wraps(test_func)
    def _wrapper(*args, **kwargs):
        from pysmt.environment import reset_env

        reset_env()
        return test_func(*args, **kwargs)

    return _wrapper


@pytest.fixture
def chc_sys_lia():
    return CHCSystem(logic=QF_UFLIA)


@pytest.fixture
def chc_sys_lra():
    return CHCSystem(logic=QF_UFLRA)


@reset_pysmt_env
@run_chc_solver
def test_system_creation(chc_sys_lia):
    assert chc_sys_lia.get_logic() == QF_UFLIA
    assert chc_sys_lia.get_predicates() == set()
    assert chc_sys_lia.get_clauses() == set()
    return chc_sys_lia


@reset_pysmt_env
@run_chc_solver
def test_add_predicate_valid1(chc_sys_lia):
    inv = Predicate("inv", [INT])
    chc_sys_lia.add_predicate(inv)
    assert inv in chc_sys_lia.get_predicates()
    return chc_sys_lia


@reset_pysmt_env
@run_chc_solver
def test_add_predicate_valid2(chc_sys_lra):
    inv = Predicate("inv", [INT])  # type of arguments is not checked
    chc_sys_lra.add_predicate(inv)
    assert inv in chc_sys_lra.get_predicates()
    return chc_sys_lra


@reset_pysmt_env
def test_add_predicate_invalid1(chc_sys_lia):
    p = Symbol("p", BOOL)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lia.add_predicate(p)


@reset_pysmt_env
def test_add_predicate_invalid2(chc_sys_lra):
    p = Symbol("p", REAL)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_predicate(p)


@reset_pysmt_env
def test_add_predicate_invalid3(chc_sys_lra):
    p = None
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_predicate(p)


@reset_pysmt_env
def test_add_predicate_invalid4(chc_sys_lra):
    p = 42
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_predicate(p)


@reset_pysmt_env
def test_add_predicate_invalid5(chc_sys_lia):
    p = Symbol("p", FunctionType(INT, [INT]))
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lia.add_predicate(p)


@reset_pysmt_env
def test_add_predicate_invalid6(chc_sys_lra):
    inv2 = Predicate("inv2", [REAL, REAL])
    chc_sys_lra.add_predicate(inv2)
    inv1 = Predicate("inv1", [REAL])
    chc_sys_lra.add_predicate(inv1)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_predicate(inv1)


@reset_pysmt_env
@run_chc_solver
def test_shortcuts(chc_sys_lia):
    inv = Predicate("inv", [INT])
    chc_sys_lia.add_predicate(inv)
    chc_sys_lia.add_clause(head=Apply(inv, [Int(0)]))
    clauses = chc_sys_lia.get_clauses()
    assert len(clauses) == 1
    return chc_sys_lia


@reset_pysmt_env
@run_chc_solver
def test_add_clause_valid1(chc_sys_lia):
    inv = Predicate("inv", [INT])
    chc_sys_lia.add_predicate(inv)

    x = Symbol("x", INT)
    nx = Symbol("nx", INT)
    b = Symbol("b", BOOL)

    chc_sys_lia.add_clause(
        body=And(Apply(inv, [x]), Equals(nx, Plus(x, Int(1))), b),
        head=And(b, Apply(inv, [nx])),
    )

    clauses = chc_sys_lia.get_clauses()
    assert len(clauses) == 1
    assert chc_sys_lia._is_linear
    return chc_sys_lia


@reset_pysmt_env
@run_chc_solver
def test_add_clause_valid2(chc_sys_lra):
    inv_int = Predicate("inv_int", [INT])
    chc_sys_lra.add_predicate(inv_int)
    inv_real = Predicate("inv_real", [REAL])
    chc_sys_lra.add_predicate(inv_real)

    x = Symbol("x", REAL)

    chc_sys_lra.add_clause(
        body=Apply(inv_real, [x]), head=Apply(inv_real, [Plus(x, Real(1))])
    )
    clauses = chc_sys_lra.get_clauses()
    assert len(clauses) == 1
    assert chc_sys_lra._is_linear
    return chc_sys_lra


@reset_pysmt_env
@run_chc_solver
def test_add_clause_valid3(chc_sys_lra):
    inv2 = Predicate("inv2", [REAL, REAL])
    chc_sys_lra.add_predicate(inv2)
    inv1 = Predicate("inv1", [REAL])
    chc_sys_lra.add_predicate(inv1)

    x = Symbol("x", REAL)

    chc_sys_lra.add_clause(
        body=And(Apply(inv2, [Real(0), Real(2)]), Apply(inv1, [x])),
        head=Apply(inv2, [Real(10), Plus(x, Real(1))]),
    )

    chc_sys_lra.add_clause(
        body=And(Apply(inv1, [Real(0)]), Apply(inv1, [x])),
        head=Apply(inv2, [Real(10), Plus(x, Real(1))]),
    )

    clauses = chc_sys_lra.get_clauses()
    assert len(clauses) == 2
    assert not chc_sys_lra._is_linear
    return chc_sys_lra


@reset_pysmt_env
def test_add_clause_invalid1(chc_sys_lra):
    inv2 = Predicate("inv2", [REAL, REAL])
    chc_sys_lra.add_predicate(inv2)
    inv1 = Predicate("inv1", [REAL])
    chc_sys_lra.add_predicate(inv1)

    x = Symbol("x", REAL)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_clause(
            body=And(Apply(inv2, [Real(0), Real(2)]), Apply(inv1, [x])),
            head=And(Apply(inv1, [Real(0)]), Apply(inv2, [Real(10), Plus(x, Real(1))])),
        )


@reset_pysmt_env
def test_add_clause_invalid2(chc_sys_lra):
    inv2 = Predicate("inv2", [REAL, REAL])
    chc_sys_lra.add_predicate(inv2)
    inv1 = Predicate("inv1", [REAL])
    chc_sys_lra.add_predicate(inv1)

    x = Symbol("x", INT)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_clause(
            body=And(Apply(inv2, [Real(0), Real(2)]), Apply(inv1, [x])),
            head=And(Apply(inv1, [Real(0)]), Apply(inv1, [Real(10)])),
        )


@reset_pysmt_env
def test_add_clause_invalid3(chc_sys_lra):
    inv1 = Predicate("inv1", [REAL])
    x = Symbol("x", REAL)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_clause(
            body=Apply(inv1, [x]), head=Apply(inv1, [Plus(x, Real(1))])
        )


@reset_pysmt_env
def test_add_clause_invalid4(chc_sys_lra):
    inv1 = Predicate("inv1", [INT])
    chc_sys_lra.add_predicate(inv1)
    x = Symbol("x", INT)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_clause(body=Apply(inv1, [x]), head=Symbol("b", BOOL))


@reset_pysmt_env
def test_add_clause_invalid5(chc_sys_lra):
    inv1 = Predicate("inv1", [INT])
    chc_sys_lra.add_predicate(inv1)
    x = Symbol("x", INT)
    with pytest.raises(PyCHCInvalidSystemException):
        chc_sys_lra.add_clause(head=Apply(inv1, [Int(1)]))
