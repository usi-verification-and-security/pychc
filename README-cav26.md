CAV 2026 Artifact: PyCHC: a Framework for Certified Horn Solving and CHC-based Design
=======================================

## Claimed badges: Available + Functional + Reusable 

### Justification for the Functional badge:
The artifact allows for replicating the result of the experimental evaluation (Section 5 in the submitted paper).

- **Table 1** lists the issues described in
  `pychc/tests/expected_bugs.py`.
  This file includes several test cases, each corresponding to one issue reported in the table. [Section Table 1](#table-1) explains in detail how to reproduce the table.

  For the "open" issues of a solver X (first three rows), a test case shows that X fails on some inputs.

  For the "fixed" issues of a solver X (last four rows), a test case shows a failure of an old release of X, which is fixed in the latest release of X.

- CHC-COMP25 results: the reviewers can replicate the 12 Eldarica failures (ill-typed model) and the 7 Z3 failures (invalid model) discovered by PyCHC, reported at page 10.
  [Section CHC-COMP25](#chc-comp25-benchmarks) explains in detail how to reproduce these failures and to run PyCHC on all the benchmarks.


### Justification for the Reusable badge:

PyCHC is open-source (https://github.com/usi-verification-and-security/pychc) and released under the Apache2.0 licence.

The framework only depends on PySMT: other dependencies are the ones needed to compile and install external backend solvers and are listed in Dockerfile.

PyCHC includes several examples and tutorials (explained in details in [this section](#tutorials-10min)) showing how to
- design a CHC problem, run a CHC solver on it, validate the returned witnesses
- debug an invalid model showing the invalid clauses, and compare two models returned by two CHC solvers
- let several CHC solvers cooperate in a portfolio and strengthen a system given an existing model
- design the k-liveness and liveness2safety encodings using CHC solving as sub-routine

PyCHC can be used outside of this artifact, as described in [this section](#use-pychc-outside-of-this-artifact).

PyCHC source code is described in [this section](#pychc-source-code).

## Requirements
- RAM: >= 16GB
- CPU cores: >= 2
- Time (smoke test): 10min
- Time (full review): 2hours
- external connectivity: NO 

# Setup

The artifact can be run by loading and running the docker image.
```
$  docker load < pychc.tar.gz
$  docker run --rm -it pychc
```
This should open a bash in working directory `~/pychc`

# Smoke test [5min]

After [setup](#setup), run all tests with pytest. All test should pass. Expected time ~3min.
```
~/pychc#  python -m pytest pychc/tests/
```
Output should end with something like `==== 104 passed in 158.64s (0:02:38) =====`

Reproduce one z3 failure. Expected time <10s.
```
~/pychc#  python scripts/eval_chccomp.py --solver z3 scripts/z3_fails_LIA-Lin.set -N 1
```

Reproduce one eldarica failure. Expected time <10s.
```
~/pychc#  python scripts/eval_chccomp.py --solver eldarica scripts/eldarica_fails.set -N 1
```

In both cases, output should end with:
```
Analyzed benchmarks: 1

Results for z3 (/ eldarica):
	Solved benchmarks: 1
	SAT benchmarks: 1
	 -- validated: 0
	UNSAT benchmarks: 0
	 -- validated: 0
```

## Troubleshooting
If `command not found` is issued for a solver (eg `golem`, `eld`, `z3`, `cvc5`, `opensmt`, ...)
try executing `source env.sh` in `~/pychc` and then retry.
Golem, Eldarica and Z3 should be correctly installed and available in the current PATH.


----------------------------------------------------
# Full review [2 hours]

## Table 1

Table1 (page 10 in the submitted paper) lists 7 issues found in various backend solvers with the current status.
Each row is associated with a GitHub Issue, opened in the respective solver, visible as a footnote in the paper.

Test `pychc/tests/test_expected_bugs.py` monitors these issues in 17 test cases.
These test cases show that PyCHC is able to catch bugs and issues raised by externals solvers.
All 17 tests can be reproduced by running:
```
~/pychc# python -m pytest pychc/tests/test_expected_bugs.py
```

**Reviewers can look at the `pychc/tests/test_expected_bugs.py` and check that all issues listed as footnote in page 10 have a corresponding test case.**

Issues marked as "open" in Table 1 (the first three rows)
are reproduced in a test case where we expect PyCHC to raise an exception.
For example, the following test case checks that PyCHC raises a `InvalidResultException` when
validating the witness produced by Z3Spacer on input file `chc-LIA-Lin_325.smt2`.
```
def test_z3_1_issue():
    # https://github.com/Z3Prover/z3/issues/6716

    test = bench_dir / "chc-LIA-Lin_325.smt2"
    spacer = Z3CHCSolver()
    spacer.run(test)

    sys = CHCSystem.load_from_file(Path(test))
    with pytest.raises(PyCHCInvalidResultException):
        sys.validate_sat_model(spacer.get_witness(), CVC5Solver())
```

Issues marked as "fixed" in Table 1 (the last four rows)
are reproduced in a test case using two versions of the same backend solver: PyCHC is expected 
to raise an exception when using the old solver, while it should validate the result produced by the latest version.
For example, the following test case checks that PyCHC raises a `SolverException`
when running Golem0.4.0, an issue fixed in the latest Golem version.
```
@reset_pysmt_env
def test_golem_1_issue():
    # https://github.com/usi-verification-and-security/golem/issues/29

    test = bench_dir / "chc-LIA-Lin_110.smt2"
    sys = CHCSystem.load_from_file(Path(test))
    validator = CVC5Solver(proof_checker=Carcara())

    # Issue from Golem 0.4.0
    old_golem = GolemSolver(binary_path=old_bin_path / "golem-0.4.0")
    with pytest.raises(PyCHCSolverException):
        old_golem.run(test)

    # Issue is fixed in the latest Golem version
    golem = GolemSolver()
    golem.run(test)
    sys.validate_sat_model(golem.get_witness(), validator)
```


## CHC-COMP25 benchmarks [5min + 1hour]

CHC-COMP25 benchmarks are downloaded directly from https://github.com/chc-comp/chc-comp25-benchmarks.
CHC solvers can be run via PyCHC on these benchmarks via `scripts/evaluate_chccomp.py`.
The script takes as input a `.set` file similar to `LIA.set` or `LIA-Lin.set` provided by in `chc-comp25-benchmarks` repository.

### Reproducing reported failures of Eldarica and Z3 [5min]

At page 10, the paper claims: "among the CHC-COMP’25 benchmarks, we found
12 benchmarks where Eldarica returns an ill-typed model, and 7 benchmarks
where Z3-Spacer returns an invalid model".

Z3 failures can be reproduced by running
```
~/pychc#  python scripts/eval_chccomp.py --solver z3 scripts/z3_fails_LIA-Lin.set
```
Here, each test should raise an Invalid model error. The log also indicates which clause was falsified in the original model
and provides the path to a `.smt2` file with a satisfiable problem (showing that the clause is not valid).

Eldarica failures can be reproduced by running
```
~/pychc#  python scripts/eval_chccomp.py --solver eldarica scripts/eldarica_fails.set
```
Here, each test should raise a Type error.


### Running PyCHC on CHC-COMP25 benchmarks [1h]
The paper reports the number of instances that were solved by Golem, Eldarica and Z3 in the LIA and LIA-Lin categories within 30s timeouts.
This evaluation is not meant to compare the efficiency of Golem, Eldarica and Z3, rather
to show that it is possible to use PyCHC on benchmarks from the competition.
Since running all benchmarks in LIA and LIA-Lin require several hours of computation, we provide options to run a subset of them,
with a limited timeout.

For example:
- Run first 100 benchmarks from the LIA category, with a timeout of 10s, with Golem, Z3 and Eldarica.
```
~/pychc# python scripts/eval_chccomp.py ../chc-comp25-benchmarks/LIA.set --json all_results.json --solver all -N 100 --timeout 10
```
- Run first 100 benchmarks from the LIA category, with a timeout of 10s, with Golem.
```
~/pychc# python scripts/eval_chccomp.py ../chc-comp25-benchmarks/LIA-Lin.set --json golem_results.json --solver golem -N 100 --timeout 10
```
A summary of the results is printed in standard output at the end.
The .json file passed with `--json` option will also store the results.

## Tutorials [10min]

PyCHC is a framework meant to facilitate the modeling and interaction with CHC solvers.
The repository includes some examples and tutorials, showing PyCHC's functionalities.

*Reviewers can read and run the provided examples.*

```
~/pychc# python examples/sat_check.py
```
This examples shows how to
- model a CHC system and serialize it to standard output
- solve the CHC system with a CHC solver
- validate the CHC solver's resulting model with an SMT solver and a proof checker
- serialize the model in a file
- run the validation on existing files

```
~/pychc# python examples/sat_check_invalid.py
```
This example shows how to
- catch that a CHC solver returns an invalid model
- inspect the clauses that are not valid
- compare two models produced by two CHC solvers

```
~/pychc# python examples/unsat_check.py
```
This example shows how to
- instruct a solver to produce checkable unsatisfiability proofs
- validate a proof with a proof checker

```
~/pychc# python examples/cooperation.py
```
This example shows how to
- run a pool of solvers in parallel on the same input
- strengthen the clauses of a CHC system given a model returned by one solver
- solve the updated system and validate the returned model against the original system

```
~/pychc# python examples/k-liveness.py
```
This example shows how to
- model K-liveness and Liveness-to-safety reductions, starting from a transition system and a Bad property
- use as backend safety check a CHC solver


# Use PyCHC outside of this artifact

* Rebuild image from Docker file [only for x86]. The Dockerfile present in the archive allows for re-building the image of this artifact with
  ```
  docker build -t pychc .
  ```
  It downloads PyCHC from Github, and install the needed solved for the experiments, and downloads the benchmarks from the CHC-COMP25 GitHub repositories.

* Alternatively, one can clone the repository directly from GitHub https://github.com/usi-verification-and-security/pychc and install the package with:
  ```
  pip install -r requirements
  python -m pysmt install --z3 --confirm agreement
  pip -e .
  ```

  Backend solvers can be downloaded from the respective GitHub pages in the specified versions, as described in `README.md`.

  *Note*: The utility script `scripts/install_solvers.sh` installs x86 binaries from the GitHub solver releases corresponding to the desired versions.
  An ARM user should install manually the desired backend solvers and make them available in PATH.

  Note that the expected bugs (see `pychc/tests/expected_bugs.py`) can be reproduced only if the solvers have been installed in the expected version.


# PyCHC source code
```
.
├── examples                  # tutorials
│   ├── cooperation.py
│   ├── example.smt2
│   ├── k-liveness.py
│   ├── sat_check_invalid.py
│   ├── sat_check.py
│   └── unsat_check.py
├── LICENSE
├── pychc
│   ├── chc_system.py         # CHC system data structure
│   ├── environment.py
│   ├── exceptions.py
│   ├── operators.py 
│   ├── parser.py
│   ├── shortcuts.py
│   ├── solvers               # wrapper of backend solvers
│   │   ├── carcara.py
│   │   ├── chc_solver.py     # abstract interface of a CHC solver
│   │   ├── cvc5.py
│   │   ├── eldarica.py
│   │   ├── golem.py
│   │   ├── opensmt.py
│   │   ├── portfolio.py
│   │   ├── proof_checker.py
│   │   ├── smt_solver.py     # abstract interface of a SMT solver with proof production
│   │   ├── witness.py
│   │   └── z3.py
│   └── tests                 # unit tests
│       ├── common.py
│       ├── expected_bugs
│       │   ├── *.smt2
│       ├── smtlib
│       │   └── *.smt2
│       ├── test_chc_system.py
│       ├── test_expected_bugs.py
│       ├── test_mod.py
│       ├── test_sat_witness.py
│       └── test_unsat_witness.py
├── Dockerfile                 # only present in the cav26ae branch
├── pyproject.toml
├── README.md
├── README-cav26.md            # this document. only present in the cav26ae branch
├── requirements.txt
└── scripts
    ├── eldarica_fails.set     # only present in the cav26ae branch
    ├── eval_chccomp.py        # only present in the cav26ae branch
    ├── install_solvers.sh
    └── z3_fails_LIA-Lin.set   # only present in the cav26ae branch
```