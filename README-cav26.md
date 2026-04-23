CAV 2026 Artifact: PyCHC: a Framework for Certified Horn Solving and CHC-based Design
=======================================

PyCHC is a Python library that facilitates the *design* and *certified solving* of systems of Constrained Horn Clauses (CHC).
Via PyCHC, the user can invoke several backend CHC solvers and cross-validate the returned results with external SMT solvers and proof checkers.
The goals of this artifact are to show that:
- PyCHC can spot bugs and issues in existing solvers such as z3, Eldarica, and cvc5
- PyCHC is easy to use for modeling CHC systems and prototyping new algorithms based on CHC solving.

## Claimed badges: Available + Functional + Reusable 

### Justification for the Functional badge:
Reviewers can replicate the results reported in the experimental evaluation (Section 5 in the submitted paper).

- Issues described in **Table 1**. File `pychc/tests/test_expected_bugs.py` includes test cases reproducing each issue reported in the table. [This section](#table-1) explains in detail how to run the tests and reproduce the table.

- Use of PyCHC on CHC-COMP25 benchmarks. At page 10, we claim that Eldarica and Z3 return invalid results in respectively 12 and 7 benchmarks.
  [Section CHC-COMP25](#chc-comp25-benchmarks) explains in detail how to reproduce these wrong results and how to run PyCHC on all the benchmarks from the CHC-COMP25 set.


### Justification for the Reusable badge:

PyCHC is open-source (https://github.com/usi-verification-and-security/pychc) and released under the Apache 2.0 licence.

PyCHC includes several examples and tutorials (explained in detail in [this section](#tutorials-10min)) showing
the framework's main functionalities.

PyCHC depends only on PySMT. This artifact includes additional standard dependencies (see Dockerfile) needed to compile and install backend solvers (e.g., `gmp`, `cmake`, ...)

PyCHC can be used outside of this artifact, as described in [this section](#use-pychc-outside-of-this-artifact).

PyCHC source code structure is described in [this section](#pychc-source-code).

## Requirements
- RAM: >= 16GB
- CPU cores: >= 2
- Time (smoke test): 5min
- Time (full review): 2hours
- external connectivity: NO 

-----------------------------------------------------
# Setup [1min]

The artifact is distributed as a Docker image. Docker must be installed on your host machine before proceeding. Load and start the container with:
```
$  docker load < pychc.tar.gz   # imports the pre-built image from the archive
$  docker run --rm -it pychc    # starts an interactive shell inside the container
```
The `--rm` flag removes the container on exit. This should open a shell in working directory `~/pychc`.


-----------------------------------------------------
# Smoke test [5min]

Each following command should be invoked from working directory `~/pychc`.

**After completing the [Setup phase](#setup)**, run all tests with pytest. Expected time ~3min.
```
python -m pytest pychc/tests/
```
All tests should pass. Output should end with something like `==== 105 passed in 158.64s (0:02:38) =====`

Reproduce one Z3 bug. Expected time <10s.
```
python scripts/eval_chccomp.py --solver z3 scripts/z3_fails_LIA-Lin.set -N 1
```
Reproduce one Eldarica bug. Expected time <10s.
```
python scripts/eval_chccomp.py --solver eldarica scripts/eldarica_fails.set -N 1
```
In both cases, the output should include some "Validation failed" messages and should end with:
```
Analyzed benchmarks: 1

Results for z3 (/ eldarica):
	Solved benchmarks: 1
	SAT benchmarks: 1
	 -- validated: 0
	UNSAT benchmarks: 0
	 -- validated: 0
```

### Troubleshooting
If you see an `executable not found` error for a solver (e.g., `golem`, `eld`, `z3`, `cvc5`, `opensmt`, ...),
run `source env.sh` from `~/pychc` and then retry. This script adds the bundled solver binaries to your PATH.
Golem, Eldarica, and Z3 should then be correctly installed and available.

----------------------------------------------------
# Full review [2 hours]

## Table 1 [5min]

Table 1 (page 10 in the submitted paper) lists 7 issues found in various backend solvers with the current status.
Each row is associated with a GitHub Issue, opened in the respective solver, visible as a footnote in the paper.

Test `pychc/tests/test_expected_bugs.py` monitors these issues in 17 test cases.
These test cases show that PyCHC is able to catch bugs and issues raised by external solvers.
All 17 tests can be reproduced by running:
```
python -m pytest pychc/tests/test_expected_bugs.py
```

**Reviewers can look at `pychc/tests/test_expected_bugs.py` and check that all issues listed as footnotes on page 10 have a corresponding test case.**

Issues marked as "open" in Table 1 (the first three rows)
are reproduced in a test case where we expect PyCHC to raise an exception.
For example, the following test case checks that PyCHC raises an `InvalidResultException` when
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
when running Golem 0.4.0, an issue fixed in the latest Golem version.
```
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
CHC solvers can be run via PyCHC on these benchmarks via `scripts/eval_chccomp.py`.
The script takes as input a `.set` file similar to `LIA.set` or `LIA-Lin.set` provided in the `chc-comp25-benchmarks` repository.

### Reproducing reported failures of Eldarica and Z3 [5min]

At page 10, the paper claims: "among the CHC-COMP25 benchmarks, we found
12 benchmarks where Eldarica returns an ill-typed model, and 7 benchmarks
where Z3-Spacer returns an invalid model".

Such Z3 failures can be reproduced by running
```
python scripts/eval_chccomp.py --solver z3 scripts/z3_fails_LIA-Lin.set
```
Here, each test should raise an Invalid model error. The log also indicates which clause was falsified in the original model
and provides the path to a `.smt2` file with a satisfiable problem (showing that the clause is not valid).

Eldarica failures can be reproduced by running
```
python scripts/eval_chccomp.py --solver eldarica scripts/eldarica_fails.set
```
Here, each test should raise an error due to an ill-formed formula.


### Running PyCHC on CHC-COMP25 benchmarks [1h]
The paper reports the number of instances that were solved by Golem, Eldarica and Z3 in the LIA and LIA-Lin categories within 30s timeouts.
This evaluation is not meant to compare the efficiency of Golem, Eldarica and Z3, rather
to show that it is possible to use PyCHC on benchmarks from the competition.
Since running all benchmarks in LIA and LIA-Lin require several hours of computation, we provide options to run a subset of them,
with a limited timeout.

For example:
- Run first 100 benchmarks from the LIA category, with a timeout of 10s, with all solvers (Golem, Z3 and Eldarica).
```
python scripts/eval_chccomp.py ../chc-comp25-benchmarks/LIA.set --json all_results.json --solver all -N 100 --timeout 10
```
- Run first 100 benchmarks from the LIA-Lin category, with a timeout of 10s, with Golem only.
```
python scripts/eval_chccomp.py ../chc-comp25-benchmarks/LIA-Lin.set --json golem_results.json --solver golem -N 100 --timeout 10
```

Each `.smt2` file is solved with the specified solver(s) and the specified timeout; SAT results are validated with `cvc5` (with 2x the specified timeout) and, only for `golem`, UNSAT results are validated with `Carcara`.

#### How to read the output of eval_chccomp.py
The first line in the output is the number of benchmarks read in the `.set` file. For example, when using `chc-comp25-benchmarks/LIA.set`, it prints `Tot Benchmarks:  1283`.

Then, it progressively prints the benchmark being solved in lines like:
`Testing /root/chc-comp25-benchmarks/kind2-chc-benchmarks/data/DRAGON_all_e1_4022_e7_2886_000.smt2: 0/1283`.

The script terminates after processing N benchmarks (set with parameter `-N` in the script). If this parameter is unspecified, all the entries in the `.set` file are executed. At the end, it prints a summary of the solved benchmarks and their status for each solver used.
The final summary should look like:
```
Analyzed benchmarks: 100

Results for z3:
	Solved benchmarks: 96
	SAT benchmarks: 62
	 -- validated: 60
	UNSAT benchmarks: 34
	 -- validated: 0

Results for eldarica:
	Solved benchmarks: 8
	SAT benchmarks: 4
	 -- validated: 4
	UNSAT benchmarks: 4
	 -- validated: 0

Results for golem:
	Solved benchmarks: 93
	SAT benchmarks: 60
	 -- validated: 60
	UNSAT benchmarks: 33
	 -- validated: 33
```

In this context, SAT means the CHC system is satisfiable (a model was found) and UNSAT means it is unsatisfiable (a proof was produced). The `-- validated` rows show how many of those results were independently verified by PyCHC.

For `golem`, all SAT and UNSAT benchmarks should be validated.

For `z3` and `eldarica`, instead,
- the number of validated SAT benchmarks might be lower
  than the number of solved SAT benchmarks because (as described in [the previous section](#reproducing-reported-failures-of-eldarica-and-z3-5min)) these solvers produce invalid results for some benchmarks, and validation might time-out for `z3`.
- the number of validated UNSAT benchmarks is always 0, since these solvers do not support proof production for UNSAT results.


## Tutorials [10min]

PyCHC is a framework meant to facilitate the design of CHC systems and the interaction with CHC solvers.
The repository includes some examples showing PyCHC's functionalities.

**Reviewers can read and run the following examples.**

```
python examples/sat_check.py
```
This example shows how to
- model a CHC system and serialize it to standard output
- solve the CHC system with a CHC solver
- validate the CHC solver's resulting model with an SMT solver and a proof checker
- serialize the model in a file
- run the validation on existing files

```
python examples/sat_check_invalid.py
```
This example shows how to
- catch that a CHC solver returns an invalid model
- inspect the clauses that are not valid
- compare two models produced by two CHC solvers

```
python examples/unsat_check.py
```
This example shows how to
- instruct a solver to produce checkable unsatisfiability proofs
- validate a proof with a proof checker

```
python examples/cooperation.py
```
This example shows how to
- run a pool of solvers in parallel on the same input
- strengthen the clauses of a CHC system given a model returned by one solver
- solve the updated system and validate the returned model against the original system

```
python examples/k-liveness.py
```
This example shows how to
- model K-liveness and Liveness-to-safety reductions, starting from a transition system and a Bad property
- use as backend safety check a CHC solver


## Use PyCHC outside of this artifact

* Rebuild image from Dockerfile [only for x86]. The Dockerfile present in the archive allows for re-building the image of this artifact with
  ```
  docker build -t pychc .
  ```
  It downloads PyCHC from GitHub, installs the needed solvers for the experiments, and downloads the benchmarks from the CHC-COMP25 GitHub repositories.

* Alternatively, one can clone the repository directly from GitHub https://github.com/usi-verification-and-security/pychc and install the package with (Python 3.12 or later is required):
  ```
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
├── README-cav26.md            # this document. only present in the cav26ae branch
├── requirements.txt
└── scripts
    ├── eldarica_fails.set     # only present in the cav26ae branch
    ├── eval_chccomp.py        # only present in the cav26ae branch
    ├── install_solvers.sh
    └── z3_fails_LIA-Lin.set   # only present in the cav26ae branch
```
