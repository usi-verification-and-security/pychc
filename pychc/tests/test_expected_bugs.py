import pytest
import logging

from pathlib import Path

from pysmt.logics import LIA
from pysmt.oracles import get_logic

from pychc.shortcuts import read_from_file
from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException
from pychc.solvers.golem import GolemSolver
from pychc.solvers.opensmt import OpenSMTSolver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.carcara import Carcara
from pychc.solvers.witness import SatWitness, Status

from pychc.tests.common import reset_pysmt_env

bench_dir = Path(__file__).parent / "expected_bugs"

old_bin_path = bench_dir / "old_binaries"

### Spacer / Z3

@reset_pysmt_env
def test_z3_1_issue():
    test = bench_dir / "chc-LIA-Lin_325.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    sys.serialize(Path("tmp.smt2"))
    spacer = Z3CHCSolver()
    validator = CVC5Solver(logic=sys.get_logic())
    spacer.set_smt_validator(validator)
    spacer.load_system(sys)
    with pytest.raises(PyCHCInvalidResultException):
        spacer.solve(validate=True)

@reset_pysmt_env
def test_z3_1_model_issue():
    test = bench_dir / "chc-LIA-Lin_325.smt2"
    model = bench_dir / "model_z3_1.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    model = SatWitness.load_from_file(Path(model))
    validator = CVC5Solver(logic=sys.get_logic())
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(model, validator)

@reset_pysmt_env
def test_z3_2_issue():
    test = bench_dir / "chc-LIA_361.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    sys.serialize(Path("tmp.smt2"))
    spacer = Z3CHCSolver()
    validator = CVC5Solver(logic=sys.get_logic())
    spacer.set_smt_validator(validator)
    spacer.load_system(sys)
    with pytest.raises(PyCHCInvalidResultException):
        spacer.solve(validate=True)

@reset_pysmt_env
def test_z3_2_model_issue():
    test = bench_dir / "chc-LIA_361.smt2"
    model = bench_dir / "model_z3_2.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    model = SatWitness.load_from_file(Path(model))
    validator = CVC5Solver(logic=sys.get_logic())
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(model, validator)

### Eldarica

@reset_pysmt_env
def test_eldarica_issue():
    test = bench_dir / "eldarica.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    validator = CVC5Solver(logic=sys.get_logic())
    
    # Issue from Eldarica 2.0.9
    old_eldarica = EldaricaSolver(
        binary_path=old_bin_path / "eldarica",
        smt_validator=validator
        )
    old_eldarica.load_system(sys)
    with pytest.raises(PyCHCSolverException):
        old_eldarica.solve(validate=True)

    # Issue is fixed in the latest Eldarica version    
    eldarica = EldaricaSolver(
        smt_validator=validator
        )
    eldarica.load_system(sys)
    eldarica.solve(validate=True)

### Golem

@reset_pysmt_env
def test_golem_1_issue():
    test = bench_dir / "chc-LIA-Lin_110.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    validator = CVC5Solver(logic=sys.get_logic())

    # Issue from Golem 0.4.0
    old_golem = GolemSolver(
        binary_path=old_bin_path,
        smt_validator=validator
        )
    old_golem.load_system(sys)
    with pytest.raises(PyCHCSolverException):
        old_golem.solve(validate=True)

    # Issue is fixed in the latest Golem version
    golem = GolemSolver(
        smt_validator=validator
    )
    golem.load_system(sys)
    golem.solve(validate=True)

@reset_pysmt_env
def test_golem_2_issue():
    test = bench_dir / "chc-LIA-Lin_307.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    validator = CVC5Solver(logic=sys.get_logic())

    # Issue from Golem 0.4.0
    old_golem = GolemSolver(
        binary_path=old_bin_path,
        smt_validator=validator
        )
    old_golem.load_system(sys)
    with pytest.raises(PyCHCSolverException):
        old_golem.solve(validate=True)

    # Issue is fixed in the latest Golem version
    golem = GolemSolver(
        smt_validator=validator
    )
    golem.load_system(sys)
    golem.solve(validate=True)

@reset_pysmt_env
def test_golem_3_issue():
    test = bench_dir / "chc-LIA-Lin_314.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    validator = CVC5Solver(logic=sys.get_logic())

    # Issue from Golem 0.4.0
    old_golem = GolemSolver(
        binary_path=old_bin_path,
        smt_validator=validator
        )
    old_golem.load_system(sys)
    with pytest.raises(PyCHCSolverException):
        old_golem.solve(validate=True)

    # Issue is fixed in the latest Golem version
    golem = GolemSolver(
        smt_validator=validator
    )
    golem.load_system(sys)
    golem.solve(validate=True)

### OpenSMT

@reset_pysmt_env
def test_opensmt_issue():
    test = bench_dir / "opensmt.smt2"
    f = read_from_file(Path(test))
    
    # Issue from OpenSMT 2.5.0
    old_opensmt = OpenSMTSolver(
        logic=get_logic(f),
        binary_path=old_bin_path
        )
    with pytest.raises(PyCHCSolverException):
        sat = old_opensmt.is_sat(f)

    # Issue is fixed in the latest OpenSMT version
    opensmt = OpenSMTSolver(logic=get_logic(f))
    sat = opensmt.is_sat(f)
    assert not sat

### CVC5

@reset_pysmt_env
def test_cvc5_1_issue():
    test = bench_dir / "cvc5_simple.smt2"
    f = read_from_file(Path(test))

    # Issue from CVC5 1.0.5
    old_cvc5 = CVC5Solver(
        logic=get_logic(f),
        binary_path=old_bin_path,
        proof_checker=Carcara()
        )
    with pytest.raises(PyCHCSolverException):
        sat = old_cvc5.is_sat(f)

    # Issue is fixed in the latest CVC5 version
    cvc5 = CVC5Solver(
        logic=get_logic(f),
        proof_checker=Carcara(),
        )
    sat = cvc5.is_sat(f)
    assert not sat
    cvc5.validate_proof()

@reset_pysmt_env
def test_cvc5_2_issue():
    test = bench_dir / "cvc5_simple_2.smt2"
    f = read_from_file(Path(test))

    # Issue from CVC5 1.0.5
    old_cvc5 = CVC5Solver(
        logic=get_logic(f),
        binary_path=old_bin_path,
        proof_checker=Carcara()
        )
    sat = old_cvc5.is_sat(f)
    with pytest.raises(PyCHCInvalidResultException):
        old_cvc5.validate_proof()

    # Issue is fixed in the latest CVC5 version
    cvc5 = CVC5Solver(
        logic=get_logic(f),
        proof_checker=Carcara(),
        )
    sat = cvc5.is_sat(f)
    assert not sat
    cvc5.validate_proof()

