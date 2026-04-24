CAV 2026 Artifact: PyCHC: a Framework for Certified Horn Solving and CHC-based Design
=======================================

This README file can be visualized nicely [here](https://github.com/usi-verification-and-security/pychc/blob/cav26ae/README-cav26.md).

## Introduction

PyCHC is a Python library available [here](https://github.com/usi-verification-and-security/pychc) that facilitates the *design* and *certified solving* of systems of constrained Horn clauses (CHC).
Via PyCHC, the user can create and manipulate CHC problems, invoke several backend CHC solvers, and cross-validate the returned results with external SMT solvers and proof checkers.
This artifact is meant to show that:
- PyCHC offers an abstraction layer on top of several existing solvers and can detect bugs in them.
- PyCHC is easy to use for modelling CHC systems and prototyping new algorithms based on CHC solving.

## Claimed badges: Available + Functional + Reusable

### Justification for the Functional badge:

Reviewers can replicate the results reported in the experimental evaluation (Section 5) of the submitted paper.

- Issues described in **Table 1**. File `pychc/tests/test_expected_bugs.py` includes test cases reproducing the issues reported in the table. [This section](#table-1-5min) explains in detail how to run these tests cases.

- Use of PyCHC on CHC-COMP25 benchmarks. At page 10, we claim that Eldarica and Z3 return invalid results in 12 and 7 benchmarks, respectively.
  [This section](#chc-comp25-benchmarks-5min--1hour) explains in detail how to reproduce these wrong results and how to run PyCHC on all the benchmarks from the CHC-COMP25 set.

- Integration of backend solvers (**Figure 1**) in the complete validation flow (**Figure 3**).
  Files `pychc/tests/test_sat_witness.py` and `pychc/tests/test_unsat_witness.py` test
  the use of all available solvers in the validation flows as explained in [this section](#figure-1-2min).

### Justification for the Reusable badge:

- [PyCHC](https://github.com/usi-verification-and-security/pychc) is open-source and released under the Apache 2.0 licence.
- PyCHC includes several examples and tutorials (explained in detail in
  [this section](#tutorials-10min)) showing the framework's main functionalities.
- PyCHC depends only on [PySMT](https://github.com/pysmt/pysmt). This artifact includes additional standard dependencies (see [Dockerfile](https://github.com/usi-verification-and-security/pychc/blob/cav26ae/Dockerfile)) needed to download, compile, and install backend solvers (e.g., `gmp`, `cmake`, `cargo`, ...).
- PyCHC can be used outside of this artifact, as described in [this section](#use-pychc-outside-of-this-artifact).
- PyCHC source code structure is described in [this section](#pychc-source-code).

## Requirements
- RAM: >= 16 GB
- CPU cores: >= 2
- Time (smoke test): 5 minutes
- Time (full review): 2 hours
- external connectivity: NO 

-----------------------------------------------------

# Setup [1min]

The artifact is distributed as a Docker image. Docker must be installed on your host machine before proceeding. Load and start the container with:
```bash
docker load < pychc.tar.gz   # imports the pre-built image from the archive
docker run --rm -it pychc    # starts an interactive shell inside the container
```
The `--rm` flag removes the container on exit. This should open a shell in working directory `~/pychc`.

-----------------------------------------------------

# Smoke test [5min]

Each following command should be invoked from working directory `~/pychc`.

**After completing the [Setup phase](#setup)**, run all tests with pytest. Expected time: ~3min.
```bash
python -m pytest pychc/tests/
```
All tests should pass. Output should end with a message similar to `==== 105 passed in 158.64s (0:02:38) =====`.

Reproduce one Z3 bug. Expected time: <10s.
```bash
python scripts/eval_chccomp.py --solver z3 scripts/z3_fails_LIA-Lin.set -N 1
```
Reproduce one Eldarica bug. Expected time: <10s.
```bash
python scripts/eval_chccomp.py --solver eldarica scripts/eldarica_fails.set -N 1
```
In both cases, the output should include some "Validation failed" messages and should end with:
```
Analyzed benchmarks: 1

Results for z3 (/ eldarica):
	Solved benchmarks: 1
	SAT benchmarks: 1
	 -- validated: 0/1
	UNSAT benchmarks: 0
	 -- validated: 0/0
```

### Troubleshooting

If you see an `executable not found` error for a solver (e.g., `golem`, `eld`, `z3`, `cvc5`, `opensmt`, ...),
run `source env.sh` from `~/pychc` and then retry. This script adds the bundled solver binaries to your PATH.
Golem, Eldarica, and Z3 should then be correctly installed and available.

----------------------------------------------------

# Full review [2 hours]

## Figure 1 [2min]

Figure 1 (page 4 in the submitted paper) shows the tool's architecture with the supported backend solvers.
Reviewers can see that all these solvers are available and usable by running the following tests.

- Test SAT model validation flow (left-hand side of Fig. 3) with all available solvers:
  ```bash
  python -m pytest pychc/tests/test_sat_witness.py
  ```
  Here, all possible combinations of CHC solvers (Eldarica, Golem, Z3) x SMT solvers (OpenSMT, Z3, cvc5) x Proof formats (none, ALETHE, LFSC, DOT) are tested on three satisfiable inputs.
  ALETHE proofs are checked by Carcara.

- Test UNSAT proof validation flow (right-hand side of Fig. 3) with all available solvers:
  ```bash
  python -m pytest pychc/tests/test_unsat_witness.py
  ```
  Here, all possible combinations of CHC solvers (Eldarica, Golem, Z3) x Proof formats (none, ALETHE, Legacy, Intermediate) are tested on two unsatisfiable inputs.
  ALETHE proofs are checked by Carcara.

## Table 1 [5min]

Table 1 (page 10 in the submitted paper) lists 7 issues found in various backend solvers with the current status.
Each row is associated with a GitHub Issue, opened in the respective solver's repository, visible as a footnote in the paper.

File `pychc/tests/test_expected_bugs.py` includes test cases that monitor such issues.

| Solver    | Issue                                                             | status | tests in `test_expected_bugs.py` |
| ----------|-------------------------------------------------------------------| ----- | ---- |
| Eldarica  | https://github.com/uuverifiers/eldarica/issues/51                 | Open  |  `test_eldarica_issue(), test_eldarica_issue2()`
| Golem     | https://github.com/usi-verification-and-security/golem/issues/161 | Open  | `test_golem_proof_production_issue()`
| Z3-Spacer | https://github.com/Z3Prover/z3/issues/6716                        | Open  | `test_z3_1_issue(), test_z3_1_model_issue(), test_z3_2_issue()`
| CVC5      | https://github.com/cvc5/cvc5/issues/9770                          | Fixed | `test_cvc5_1_issue()`
| Golem     | http://github.com/usi-verification-and-security/golem/issues/29   | Fixed | `test_golem_1_issue()`
| Golem     | https://github.com/usi-verification-and-security/golem/issues/27  | Fixed | `test_golem_2_issue()`
| OpenSMT   | https://github.com/usi-verification-and-security/opensmt/issues/613 | Fixed | `test_opensmt_issue()`

All test cases can be run with:
```bash
python -m pytest pychc/tests/test_expected_bugs.py
```

Issues marked as "open" in Table 1 (the first three rows)
are reproduced by test cases where PyCHC should raise an exception.
For example, the following test case passes only if PyCHC raises
an `InvalidResultException` when validating the witness produced
by Z3-Spacer on input file `chc-LIA-Lin_325.smt2`.

```python
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
are reproduced by test cases using two versions of the same backend solver: PyCHC should 
to raise an exception when using the old solver, while it should validate the result produced by the latest version.
For example, the following test case passes only if PyCHC detects a `SolverException`
when running Golem 0.4.0, and the latest version of Golem runs without errors.

```python
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

The file also includes some extra test cases that are not mentioned in the Table (eg., `test_golem_seg_fault_issue()` reproduces a bug fixed with [this commit](https://github.com/usi-verification-and-security/golem/commit/50f3b1a), without a connected issue, and was not
explicitly mentioned in the paper).

## CHC-COMP25 benchmarks [5min + 1h]

CHC-COMP25 benchmarks are downloaded directly from https://github.com/chc-comp/chc-comp25-benchmarks.
CHC solvers can be run via PyCHC on these benchmarks via `scripts/eval_chccomp.py`.
The script takes as input a `.set` file similar to `LIA.set` or `LIA-Lin.set` provided in the `chc-comp25-benchmarks` repository.

### Reproducing reported failures of Eldarica and Z3 [5min]

At page 10, the paper claims: "among the CHC-COMP25 benchmarks, we found
12 benchmarks where Eldarica returns an ill-typed model, and 7 benchmarks
where Z3-Spacer returns an invalid model".

The 7 Z3 failures can be reproduced by running
```bash
python scripts/eval_chccomp.py --solver z3 scripts/z3_fails_LIA-Lin.set
```
In these tests, Z3 produces an invalid model. The log also indicates which clause was falsified in the original model
and provides the path to a `.smt2` file with a satisfiable problem (showing that the clause is not valid).

The 12 Eldarica failures can be reproduced by running
```bash
python scripts/eval_chccomp.py --solver eldarica scripts/eldarica_fails.set
```
In these tests, Eldarica returns the model as a non-well-formed formula.

### Running PyCHC on CHC-COMP25 benchmarks [1h]

The paper reports the number of instances that were solved by Golem, Eldarica, and Z3 in the LIA and LIA-Lin categories within 30s timeouts.
This evaluation is not meant to compare the efficiency of Golem, Eldarica, and Z3, rather
to show that it is possible to use PyCHC on benchmarks from the competition.
Since running all benchmarks in LIA and LIA-Lin would require several hours of computation, we provide options to run a subset of them,
with a limited timeout.

For example:
- Run first 100 benchmarks from the LIA category, with a timeout of 10s, with all solvers (Golem, Z3, and Eldarica).
```bash
python scripts/eval_chccomp.py ../chc-comp25-benchmarks/LIA.set --solver all -N 100 --timeout 10
```
- Run first 400 benchmarks from the LIA-Lin category, with a timeout of 10s, with Golem only.
```bash
python scripts/eval_chccomp.py ../chc-comp25-benchmarks/LIA-Lin.set --solver golem -N 400 --timeout 10
```

Results are progressively printed in a `.json` file. If the script is interrupted, it is possible to resume the computation by launching it again with option `--resume` and only the missing benchmarks will be re-executed.

#### How to read the output of eval_chccomp.py

Each `.smt2` file is solved with the specified solver(s) and the specified timeout; SAT models are validated with `cvc5` (with 2x the specified timeout) and, only for `golem`, UNSAT proofs are validated with `Carcara`.

The script terminates after processing N benchmarks (set with parameter `-N` in the script). If this parameter is unspecified, all the entries in the `.set` file are executed. At the end, it prints a summary of the solved benchmarks and their status for each solver used.
The `-- validated: X/Y` lines indicate that `X` out of `Y` results were validated by PyCHC.

For `golem`, all SAT and UNSAT benchmarks should be validated.

For `z3` and `eldarica`, instead,
- the number of validated SAT results may be lower than the solved instances because (as described in [the previous section](#reproducing-reported-failures-of-eldarica-and-z3-5min)) these solvers produce invalid results for some benchmarks, and validation might time-out for `z3`;
- the number of validated UNSAT results is always 0, since these solvers do not support proof production for UNSAT results.

## Tutorials [10min]

PyCHC is a framework meant to facilitate the design of CHC systems and the interaction with CHC solvers.
The repository includes some examples showing PyCHC's functionalities.

**Reviewers can read and run the following examples.**

```bash
python examples/sat_check.py
```
This example shows how to
- model a CHC system and serialize it to standard output;
- solve the CHC system with a CHC solver;
- validate the CHC solver's resulting model with an SMT solver and a proof checker;
- serialize the model in a file;
- run the validation on existing files.

```bash
python examples/sat_check_invalid.py
```
This example shows how to
- catch that a CHC solver returns an invalid model;
- inspect the clauses that are not valid;
- compare two models produced by two CHC solvers.

```bash
python examples/unsat_check.py
```
This example shows how to
- instruct a solver to produce checkable unsatisfiability proofs;
- validate a proof with a proof checker.

```bash
python examples/cooperation.py
```
This example shows how to
- run a pool of solvers in parallel on the same input;
- strengthen the clauses of a CHC system given a model returned by one solver;
- solve the updated system and validate the returned model against the original system.

```bash
python examples/k-liveness.py
```
This example shows how to
- model K-liveness and liveness-to-safety reductions, starting from a transition system and a Bad property;
- use as backend safety check a CHC solver.

## Use of PyCHC outside of this artifact

* This image was created with [this Dockerfile](https://github.com/usi-verification-and-security/pychc/blob/cav26ae/Dockerfile) on a x86 architecture, with
  ```bash
  docker build -t pychc .
  ```
  The Dockerfile downloads PyCHC (branch cav26ae) from GitHub, installs the needed solvers for the experiments, and downloads the benchmarks from the CHC-COMP25 GitHub repositories.

* PyCHC can be used by cloning from [GitHub](https://github.com/usi-verification-and-security/pychc) and installing the package with (Python 3.12 or later is required)
  ```bash
  pip install -r requirements.txt
  python -m pysmt install --z3 --confirm agreement
  pip install -e .
  ```

  Backend solvers can be downloaded from the respective GitHub pages in the specified versions, as described in `README.md`.

  *Note*: The utility script `scripts/install_solvers.sh` installs x86 binaries from the GitHub solver releases corresponding to the desired versions.
  An ARM user should manually install the desired backend solvers and make them available in PATH.

  Note that the expected bugs (see `pychc/tests/test_expected_bugs.py`) can be reproduced only if the solvers have been installed in the expected version.


## PyCHC source code

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
├── README-cav26.md            # this document, only present in the cav26ae branch
├── requirements.txt
└── scripts
    ├── eldarica_fails.set     # only present in the cav26ae branch
    ├── eval_chccomp.py        # only present in the cav26ae branch
    ├── install_solvers.sh
    └── z3_fails_LIA-Lin.set   # only present in the cav26ae branch
```
