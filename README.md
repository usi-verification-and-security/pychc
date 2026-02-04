# PyCHC: A library for certified CHC solving

PyCHC is a solver-agnostic Python library for
the *design* and *certified solving* of systems of Constrained Horn Clauses (CHC).

__Design__: PyCHC provides intuitive Python APIs to create and manipulate
CHC systems programmatically, and solve them using different backend CHC solvers.
It provides an abstraction layer over state-of-the-art CHC solvers,
(such as <a href="https://github.com/Z3Prover/z3">Z3-Spacer</a>, <a href="https://github.com/uuverifiers/eldarica">Eldarica</a>, and <a href="https://github.com/usi-verification-and-security/golem">Golem</a>) hiding the
solver-specific details from the user, and enabling to
investigate the produced results in a uniform way.
As a consequence, PyCHC enables rapid prototyping of new CHC-based algorithms
and experimentation with novel strategies for cooperative solving.
PyCHC leverages the <a href="https://github.com/pysmt/pysmt">PySMT</a> library for SMT formula manipulation and interaction
with SMT solvers.

__Result Certification__: PyCHC offers a certification pipeline to validate the correctness of results reported by the CHC solvers, via the use of independent
tools:
satisfiable results are validated with SMT solvers
(such as <a href="https://github.com/cvc5/cvc5">CVC5</a>, <a href="https://github.com/usi-verification-and-security/opensmt">OpenSMT</a>, or <a href="https://github.com/Z3Prover/z3">Z3</a>),
while unsatisfiable proofs are validated with proof checkers
(such as <a href="https://github.com/ufmg-smite/carcara">Carcara</a>).

PyCHC implements the validation techniques presented in the papers:
- Otoni, R., Blicha, M., Eugster, P., Sharygina, N.: Validation of CHC Satisfiability
with ATHENA. Formal Aspects of Computing (FAC) 2025 https://doi.org/10.1145/3716505
- Otoni, R., Blicha, M., Rivera, M.B., Eugster, P., Kofroň, J., Sharygina, N.: Unsatisfiability Proofs for Horn Solving. TACAS 2025 https://doi.org/10.1007/978-3-031-90653-4_4

## Using PyCHC

### Design a CHC system
A new CHC system can be created programmatically using APIs such as 
`Predicate`, `Clause` and `Apply`, together with
the SMT formulae manipulation shortcuts provided by PySMT.
```python
sys = CHCSystem(logic=QF_UFLIA)    # Create a CHC system 
inv = Predicate("inv", [INT])      # Declare a predicate inv(x: Int)
sys.add_predicate(inv)             # Add predicate to the system
x = Symbol("x", INT)               # Declare variable x: Int
sys.add_clauses(                   # Add a set of clauses to the system
    {
        # init clause: inv(0)
        Clause(head=Apply(inv, [Int(0)])),
        # transition clause: inv(x) & -> inv(x + 1)
        Clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))])),
        # goal clause: inv(x) & x < 0 -> FALSE
        Clause(body=And(Apply(inv, [x]), LT(x, Int(0))), head=FALSE()),
    }
)
```

### Certified solving of CHC systems
Once a CHC system is created or loaded from a `smt2` file, it can be solved using different backend solver. 

A CHC solver can be equipped with SMT solvers and proof checkers
for validating the produced results.
Also SMT solvers can be accompanied with a proof-checker
validating their unsatisfiability results.

```python
# Create an instance of CVC5 SMT solver whose proofs are checked with Carcara
cvc5 = CVC5Solver(proof_checker=Carcara(), proof_format=ALETHE)
# Create an instance of the Golem CHC solver
golem = GolemSolver(
    smt_validator=cvc5,       # SMT solver for validating satisfiable results
    proof_checker=Carcara(),  # Proof checker for validating unsatisfiable results
)
golem.load_system(sys)
golem.solve(validate=True)
```

When validation is not successful, an exception is raised and a detailed log
is provided with the failure reason. For example, the following log 
is produced by running <a href="https://github.com/usi-verification-and-security/pychc/blob/master/examples/sat_check_invalid.py">examples/sat_check_invalid.py</a>

```
ERROR:Falsified clause: (forall A, B, C, D, E, F . ((h8(A, B, C, D, E, F) & True) -> h5(A, B, C, D, E, F)))
ERROR:Interpreted clause is not valid: ((True) -> ((! (D <= -1)) & (! (E <= -1))))
Validation of witness produced with Spacer failed: Invalid CHC model. Clause 5 is falsified. See satisfiable query: /tmp/tmpfile.smt2
```

### Examples and Tutorials

Other examples are provided in directory `examples`.

- <a href="https://github.com/usi-verification-and-security/pychc/blob/master/examples/sat_check.py">sat_check.py</a> shows how to certify a satisfiable CHC problem 
- <a href="https://github.com/usi-verification-and-security/pychc/blob/master/examples/sat_check_invalid.py">sat_check_invalid.py</a> shows how Z3Spacer might return an invalid model, and how to compare the models produced by different solvers
- <a href="https://github.com/usi-verification-and-security/pychc/blob/master/examples/unsat_check.py">unsat_check.py</a> shows how to certify the unsatisfiability proof produced by Golem
- <a href="https://github.com/usi-verification-and-security/pychc/blob/master/examples/cooperation.py">cooperation.py</a> shows how to run several CHC solvers in parallel in a portfolio approach and experiment with invariant sharing
- <a href="https://github.com/usi-verification-and-security/pychc/blob/master/examples/k-liveness.py">k-liveness.py</a> shows how to prototype the k-liveness and liveness2safety algorithms

## Installation

### Installing PyCHC

PyCHC only dependency is the library PySMT.

Install `pySMT` module and `z3` quantifier elimination strategy via `pysmt`.
```
$ pip install -r requirements.txt
$ python -m pysmt install --z3 --confirm-agreement
```
(Note: this installation of `z3` is used uniquely for removing
quantifiers from CHC satisfiability witnesses, when the chosen SMT validator
does not support quantifiers. It is not the `z3` binary used as backend CHC solver
or SMT validator.)

### Installing backend solvers
Install the external solver and make them available in `PATH`. These are
the versions used for development and testing:

- Z3: `4.15.0`
- Eldarica: `2.2.1`
- Golem: commit `50f3b1a` (alternatively, release `0.9.0`, although some tests could fail)
- CVC5: `1.3.2`
- OpenSMT: `2.9.2`
- Carcara: `rev b685c15` 

**For x86_64 Linux platforms**, the following does this for you.
```
$ ./scripts/install_solvers.sh
$ source env.sh
```
This script creates a directory `binaries` where the needed releases are downloaded and extracted. Compiling from source is required for <a href="https://github.com/usi-verification-and-security/golem">Golem</a> and <a href="https://github.com/ufmg-smite/carcara">Carcara</a> (see their respective repositories for additional requirements).


## Run tests

### Prerequisite: install the old versions of solvers for expected bugs tests
For running `pychc/tests/test_expected_bugs.py`, you need
to install the old version of the analyzed tools first.
The test are designed to track the status of several issues
across different versions of the backend tools.

The old versions needed are:
- Golem: `0.4.0`
- Golem: `0.9.0`
- CVC5: `1.0.5`
- OpenSMT: `2.5.0`
- Eldarica: `2.0.9`

And move the binaries to `pychc/tests/expected_bugs/old_binaries/`.

**For x86_64 Linux platforms** the following does this for you.
```
$ ./scripts/install_solvers.sh pychc/tests/expected_bugs/old_binaries/ --old-releases
```

### Running all tests
After having installed the old versions, all tests can be run with:
```
$ python -m pytest pychc/tests
```


