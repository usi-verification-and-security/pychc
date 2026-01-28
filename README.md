# pyCHC: A library for certified CHC solving

## Installation

### Installing PyCHC
Install `pySMT` module and `z3` solver via `pysmt` (needed to perform quantifier elimination)
```
pip install -r requirements.txt
python -m pysmt install --z3 --confirm-agreement
```

### Installing backend solvers
Install the external solver and make them available in `PATH`.
- Z3: `4.15.0`
- Eldarica: `2.2.1`
- Golem: commit `50f3b1a` (alternatively, release `0.9.0`, although some tests could fail)
- CVC5: `1.3.2`
- OpenSMT: `2.9.2`
- Carcara: `rev b685c15` 

**For x86_64 Linux platforms**, the following does this for you.
```
./scripts/install_solvers.sh
source env.sh
```
This script creates a directory `binaries` where the needed releases are downloaded and extracted. Compiling from source is required for Golem and Carcara (see their respective
README for additional requirements).


## Run example:

Examples are provided in directory `pychc/examples/`.

- `python -m examples.sat_check` runs simple example certifying a satisfiable CHC problem 
- `python -m examples.unsat_check` runs a simple example certifying an unsatisfiable CHC problem 
- `python -m examples.cooperative_example` runs a cooperative example, with portfolio and invariant sharing. 
- `python -m examples.k_liveness` runs a prototyping a k-liveness algorithm

## Run tests

### Installing old versions of solvers for expected bugs tests
For running `pychc/tests/test_expected_bugs.py`, you need
to install the old version of the analyzed tools first:
- Golem: `0.4.0`
- Golem: `0.9.0`
- CVC5: `1.0.5`
- OpenSMT: `2.5.0`
- Eldarica: `2.0.9`

And move the binaries to `pychc/tests/expected_bugs/old_binaries/`.

**For x86_64 Linux platforms** the following does this for you.
```
./scripts/install_solvers.sh pychc/tests/expected_bugs/old_binaries/ --old-releases
```

### Running all tests
All tests can be run with:
```
python -m pytest pychc/tests
```


