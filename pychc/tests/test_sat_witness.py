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
from pychc.shortcuts import Predicate, Apply, Clause
from pychc.exceptions import PyCHCInvalidResultException

from pychc.tests.common import reset_pysmt_env

from pychc.solvers.witness import Status, ProofFormat
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.golem import GolemSolver
from pychc.solvers.z3 import Z3CHCSolver, Z3SMTSolver
from pychc.solvers.opensmt import OpenSMTSolver
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.carcara import Carcara


ALL_OPTIONS = [
    (EldaricaSolver, OpenSMTSolver, None),
    (EldaricaSolver, Z3SMTSolver, None),
    (EldaricaSolver, CVC5Solver, ProofFormat.ALETHE),
    (EldaricaSolver, CVC5Solver, ProofFormat.LFSC),
    (EldaricaSolver, CVC5Solver, ProofFormat.DOT),
    (GolemSolver, OpenSMTSolver, None),
    (GolemSolver, Z3SMTSolver, None),
    (GolemSolver, CVC5Solver, ProofFormat.ALETHE),
    (GolemSolver, CVC5Solver, ProofFormat.LFSC),
    (GolemSolver, CVC5Solver, ProofFormat.DOT),
    (Z3CHCSolver, OpenSMTSolver, None),
    (Z3CHCSolver, Z3SMTSolver, None),
    (Z3CHCSolver, CVC5Solver, ProofFormat.ALETHE),
    (Z3CHCSolver, CVC5Solver, ProofFormat.LFSC),
    (Z3CHCSolver, CVC5Solver, ProofFormat.DOT),
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
        proof = kwargs.pop("smt_kwargs", None)

        # Run CHC solver
        chc_solver = chc_cls()

        # Instantiate SMT validator
        proof_checker = Carcara() if proof == ProofFormat.ALETHE else None
        smt_validator = smt_cls(logic=sys.get_logic(), proof_checker=proof_checker)
        chc_solver.set_smt_validator(smt_validator)

        chc_solver.load_system(sys)
        status = chc_solver.solve(validate=True)
        assert status == Status.SAT

        chc_solver.validate_witness()
        witness = chc_solver.get_witness()
        assert witness is not None

        sys.learn_from_witness(witness)

        chc_solver.load_system(sys)
        status = chc_solver.solve(validate=True)
        assert status == Status.SAT

    return _wrapper


@pytest.mark.parametrize(
    argnames=("chc_class", "smt_class", "smt_kwargs"),
    argvalues=ALL_OPTIONS,
)
@reset_pysmt_env
@run_solver
def test_system1(chc_class, smt_class, smt_kwargs):
    sys = CHCSystem(logic=QF_UFLIA)
    inv = Predicate("inv", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(inv)
    sys.add_clause(Clause(head=Apply(inv, [Int(0)])))
    sys.add_clause(Clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))])))
    sys.add_clause(Clause(body=And(Apply(inv, [x]), LT(x, Int(0))), head=FALSE()))
    return sys


@pytest.mark.parametrize(
    argnames=("chc_class", "smt_class", "smt_kwargs"),
    argvalues=ALL_OPTIONS,
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
    sys.add_clause(Clause(head=Apply(inv1, [Int(0)])))
    sys.add_clause(Clause(body=Apply(inv1, [x]), head=Apply(inv1, [Plus(x, Int(1))])))
    sys.add_clause(Clause(body=Apply(inv1, [x]), head=Apply(inv2, [Minus(Int(0), x)])))
    sys.add_clause(Clause(body=And(Apply(inv2, [x]), LT(Int(0), x)), head=FALSE()))
    return sys


@pytest.mark.parametrize(
    argnames=("chc_class", "smt_class", "smt_kwargs"),
    argvalues=ALL_OPTIONS,
)
@reset_pysmt_env
@run_solver
def test_system3(chc_class, smt_class, smt_kwargs):
    sys = CHCSystem(logic=QF_UFLIA)
    fail = Predicate("fail", [])
    inv = Predicate("inv", [INT])
    x = Symbol("x", INT)
    sys.add_predicate(fail)
    sys.add_predicate(inv)
    sys.add_clause(Clause(head=Apply(inv, [Int(0)])))
    sys.add_clause(Clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))])))
    sys.add_clause(Clause(body=And(Apply(inv, [x]), LT(x, Int(0))), head=fail))
    sys.add_clause(Clause(body=Apply(fail, []), head=FALSE()))
    return sys
