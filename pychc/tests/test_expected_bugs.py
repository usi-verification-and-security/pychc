import pytest

from pathlib import Path

from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException
from pychc.solvers.golem import GolemSolver
from pychc.solvers.opensmt import OpenSMTSolver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.carcara import Carcara
from pychc.solvers.witness import ProofFormat, SatWitness

from pychc.tests.common import reset_pysmt_env

bench_dir = Path(__file__).parent / "expected_bugs"

old_bin_path = bench_dir / "old_binaries"

### Spacer / Z3


@reset_pysmt_env
def test_z3_1_issue():
    # https://github.com/Z3Prover/z3/issues/6716

    test = bench_dir / "chc-LIA-Lin_325.smt2"
    spacer = Z3CHCSolver()
    spacer.run(test)

    sys = CHCSystem.load_from_smtlib(Path(test))
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(spacer.get_witness(), CVC5Solver())


@reset_pysmt_env
def test_z3_1_model_issue():
    # https://github.com/Z3Prover/z3/issues/6716

    test = bench_dir / "chc-LIA-Lin_325.smt2"
    model = bench_dir / "model_z3_1.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    model = SatWitness.load_from_file(Path(model))
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(model, CVC5Solver())


@reset_pysmt_env
def test_z3_2_issue():
    # https://github.com/Z3Prover/z3/issues/6716

    test = bench_dir / "chc-LIA_361.smt2"
    spacer = Z3CHCSolver()
    spacer.run(test)

    sys = CHCSystem.load_from_smtlib(Path(test))
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(spacer.get_witness(), CVC5Solver())


### Eldarica


@reset_pysmt_env
def test_eldarica_issue():
    # https://github.com/uuverifiers/eldarica/issues/51

    test = bench_dir / "eldarica.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    validator = CVC5Solver(proof_checker=Carcara())

    # Issue from Eldarica 2.0.9
    old_eldarica = EldaricaSolver(binary_path=old_bin_path / "eldarica")
    old_eldarica.run(test)
    with pytest.raises(PyCHCSolverException):
        sys.validate_sat_model(old_eldarica.get_witness(), validator)

    # Issue is fixed in the latest Eldarica version
    eldarica = EldaricaSolver()
    eldarica.run(test)
    sys.validate_sat_model(eldarica.get_witness(), validator)


### Golem


@reset_pysmt_env
def test_golem_proof_production_issue():
    # https://github.com/usi-verification-and-security/golem/issues/161

    test = bench_dir / "golem_proof_imply.smt2"
    golem = GolemSolver()
    golem.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        Carcara().validate_witness(golem.get_witness(), smt2file=test)


@reset_pysmt_env
def test_golem_seg_fault_issue():
    # Fixed in https://github.com/usi-verification-and-security/golem/commit/50f3b1a
    # This test fails if Golem is installed from release 0.9.0

    test = bench_dir / "golem_fact.smt2"
    old_golem = GolemSolver(
        binary_path=old_bin_path / "golem-0.9.0", proof_format=ProofFormat.ALETHE
    )
    with pytest.raises(PyCHCSolverException):
        old_golem.run(test)

    golem = GolemSolver(proof_format=ProofFormat.ALETHE)
    golem.run(test)


@reset_pysmt_env
def test_golem_1_issue():
    # https://github.com/usi-verification-and-security/golem/issues/29

    test = bench_dir / "chc-LIA-Lin_110.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    validator = CVC5Solver(proof_checker=Carcara())

    # Issue from Golem 0.4.0
    old_golem = GolemSolver(binary_path=old_bin_path / "golem-0.4.0")
    with pytest.raises(PyCHCSolverException):
        old_golem.run(test)

    # Issue is fixed in the latest Golem version
    golem = GolemSolver()
    golem.run(test)
    sys.validate_sat_model(golem.get_witness(), validator)


@reset_pysmt_env
def test_golem_2_issue():
    # https://github.com/usi-verification-and-security/golem/issues/27

    test = bench_dir / "chc-LIA-Lin_314.smt2"
    sys = CHCSystem.load_from_smtlib(Path(test))
    validator = CVC5Solver(proof_checker=Carcara())

    # Issue from Golem 0.4.0
    old_golem = GolemSolver(binary_path=old_bin_path / "golem-0.4.0")
    old_golem.run(test)
    with pytest.raises(PyCHCSolverException):
        sys.validate_sat_model(old_golem.get_witness(), validator)

    # Issue is fixed in the latest Golem version
    golem = GolemSolver()
    golem.run(test)
    sys.validate_sat_model(golem.get_witness(), validator)


### OpenSMT


@reset_pysmt_env
def test_opensmt_issue():
    # https://github.com/usi-verification-and-security/opensmt/issues/613

    test = bench_dir / "opensmt.smt2"

    # Issue from OpenSMT 2.5.0
    old_opensmt = OpenSMTSolver(binary_path=old_bin_path / "opensmt-2.5.0")
    with pytest.raises(PyCHCSolverException):
        old_opensmt.run(test)

    # Issue is fixed in the latest OpenSMT version
    opensmt = OpenSMTSolver()
    opensmt.run(test)
    assert not opensmt.solve()


### CVC5


@reset_pysmt_env
def test_cvc5_1_issue():
    # https://github.com/cvc5/cvc5/issues/9770

    test = bench_dir / "cvc5_simple.smt2"

    # Issue from CVC5 1.0.5
    old_cvc5 = CVC5Solver(binary_path=old_bin_path / "cvc5-1.0.5" / "bin")
    with pytest.raises(PyCHCSolverException):
        old_cvc5.run(test)

    # Issue is fixed in the latest CVC5 version
    cvc5 = CVC5Solver(proof_checker=Carcara())
    cvc5.run(test)
    assert not cvc5.solve()
    cvc5.validate_proof()
