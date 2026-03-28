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

import pytest
from pathlib import Path

from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException
from pychc.solvers.carcara import Carcara
from pychc.solvers.witness import ProofFormat, SatWitness

from common import reset_pysmt_env, cvc5_solver, eldarica_solver, golem_solver, old_cvc5_solver, old_eldarica_solver, old_golem_solver, old_opensmt_solver, opensmt_solver, z3_chc_solver

bench_dir = Path(__file__).parent / "expected_bugs"


### Spacer / Z3


@reset_pysmt_env
def test_z3_1_issue():
    # https://github.com/Z3Prover/z3/issues/6716
    test = bench_dir / "chc-LIA-Lin_325.smt2"
    spacer = z3_chc_solver()
    spacer.run(test)

    sys = CHCSystem.load_from_file(Path(test))
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(spacer.get_witness(), cvc5_solver())


@reset_pysmt_env
def test_z3_1_model_issue():
    # https://github.com/Z3Prover/z3/issues/6716

    test = bench_dir / "chc-LIA-Lin_325.smt2"
    model = bench_dir / "model_z3_1.smt2"
    sys = CHCSystem.load_from_file(Path(test))
    model = SatWitness.load_from_file(Path(model))
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(model, cvc5_solver())


@reset_pysmt_env
def test_z3_2_issue():
    # https://github.com/Z3Prover/z3/issues/6716

    test = bench_dir / "chc-LIA_361.smt2"
    spacer = z3_chc_solver()
    spacer.run(test)

    sys = CHCSystem.load_from_file(Path(test))
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(spacer.get_witness(), cvc5_solver())


### Eldarica


@reset_pysmt_env
def test_eldarica_issue():
    # https://github.com/uuverifiers/eldarica/issues/51

    test = bench_dir / "eldarica.smt2"
    sys = CHCSystem.load_from_file(Path(test))
    validator = cvc5_solver(proof_checker=Carcara())

    # Issue from Eldarica 2.0.9
    old_eldarica = old_eldarica_solver()
    old_eldarica.run(test)
    with pytest.raises(PyCHCSolverException):
        sys.validate_sat_model(old_eldarica.get_witness(), validator)

    # Issue is fixed in the latest Eldarica version
    eldarica = eldarica_solver()
    eldarica.run(test)
    sys.validate_sat_model(eldarica.get_witness(), validator)


### Golem


@reset_pysmt_env
def test_golem_proof_production_issue():
    # https://github.com/usi-verification-and-security/golem/issues/161

    test = bench_dir / "golem_proof_imply.smt2"
    golem = golem_solver()
    golem.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        Carcara().validate_witness(golem.get_witness(), smt2file=test)


@reset_pysmt_env
def test_golem_seg_fault_issue():
    # Fixed in https://github.com/usi-verification-and-security/golem/commit/50f3b1a
    # This test fails if Golem is installed from release 0.9.0

    test = bench_dir / "golem_fact.smt2"
    old_golem = old_golem_solver(proof_format=ProofFormat.ALETHE)
    with pytest.raises(PyCHCSolverException):
        old_golem.run(test)

    golem = golem_solver(proof_format=ProofFormat.ALETHE)
    golem.run(test)


@reset_pysmt_env
def test_golem_1_issue():
    # https://github.com/usi-verification-and-security/golem/issues/29

    test = bench_dir / "chc-LIA-Lin_110.smt2"
    sys = CHCSystem.load_from_file(Path(test))
    validator = cvc5_solver(proof_checker=Carcara())

    # Issue from Golem 0.4.0
    old_golem = old_golem_solver()
    with pytest.raises(PyCHCSolverException):
        old_golem.run(test)

    # Issue is fixed in the latest Golem version
    golem = golem_solver()
    golem.run(test)
    sys.validate_sat_model(golem.get_witness(), validator)


@reset_pysmt_env
def test_golem_2_issue():
    # https://github.com/usi-verification-and-security/golem/issues/27

    test = bench_dir / "chc-LIA-Lin_314.smt2"
    sys = CHCSystem.load_from_file(Path(test))
    validator = cvc5_solver(proof_checker=Carcara())

    # Issue from Golem 0.4.0
    old_golem = old_golem_solver()
    old_golem.run(test)
    with pytest.raises(PyCHCSolverException):
        sys.validate_sat_model(old_golem.get_witness(), validator)

    # Issue is fixed in the latest Golem version
    golem = golem_solver()
    golem.run(test)
    sys.validate_sat_model(golem.get_witness(), validator)


### OpenSMT


@reset_pysmt_env
def test_opensmt_issue():
    # https://github.com/usi-verification-and-security/opensmt/issues/613

    test = bench_dir / "opensmt.smt2"

    # Issue from OpenSMT 2.5.0
    old_opensmt = old_opensmt_solver()
    with pytest.raises(PyCHCSolverException):
        old_opensmt.run(test)

    # Issue is fixed in the latest OpenSMT version
    opensmt = opensmt_solver()
    opensmt.run(test)
    assert not opensmt.solve()


### CVC5

@reset_pysmt_env
def test_cvc5_proof_0_issue():

    test = bench_dir / "cvc5_simple_resolution.smt2"

    cvc5 = cvc5_solver(proof_checker=Carcara())
    cvc5.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        cvc5.validate_proof()

@reset_pysmt_env
def test_cvc5_proof_diseq_issue_1():

    test = bench_dir / "cvc5_simple_diseq_1.smt2"

    cvc5 = cvc5_solver(proof_checker=Carcara())
    cvc5.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        cvc5.validate_proof()

@reset_pysmt_env
def test_cvc5_proof_diseq_issue_2():

    test = bench_dir / "cvc5_simple_diseq_2.smt2"

    cvc5 = cvc5_solver(proof_checker=Carcara())
    cvc5.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        cvc5.validate_proof()

@reset_pysmt_env
def test_cvc5_proof_diseq_issue_3():

    test = bench_dir / "cvc5_simple_diseq_3.smt2"

    cvc5 = cvc5_solver(proof_checker=Carcara())
    cvc5.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        cvc5.validate_proof()

@reset_pysmt_env
def test_cvc5_proof_diseq_issue_4():

    test = bench_dir / "cvc5_simple_diseq_4.smt2"

    cvc5 = cvc5_solver(proof_checker=Carcara())
    cvc5.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        cvc5.validate_proof()

@reset_pysmt_env
def test_cvc5_proof_diseq_issue_5():

    test = bench_dir / "cvc5_simple_diseq_5.smt2"

    cvc5 = cvc5_solver(proof_checker=Carcara())
    cvc5.run(test)
    with pytest.raises(PyCHCInvalidResultException):
        cvc5.validate_proof()

@reset_pysmt_env
def test_cvc5_1_issue():
    # https://github.com/cvc5/cvc5/issues/9770

    test = bench_dir / "cvc5_simple.smt2"

    # Issue from CVC5 1.0.5
    old_cvc5 = old_cvc5_solver()
    with pytest.raises(PyCHCSolverException):
        old_cvc5.run(test)

    # Issue is fixed in the latest CVC5 version
    cvc5 = cvc5_solver(proof_checker=Carcara())
    cvc5.run(test)
    assert not cvc5.solve()
    cvc5.validate_proof()
