from pathlib import Path

from pychc.solvers.witness import UnsatWitness, ProofFormat
from pychc.chc_system import CHCSystem
from pychc.solvers import golem, carcara, opensmt
from pychc.exceptions import PyCHCException

from pysmt.typing import INT
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import And, Symbol, Int, Plus, FALSE, GE
from pychc.shortcuts import Predicate, Apply, Clause

import logging
logging.basicConfig(level=logging.DEBUG)

# Create a CHC system
sys = CHCSystem(logic=QF_UFLIA)

# Create a predicate inv(x: Int)
inv = Predicate("inv", [INT])
sys.add_predicate(inv)

x = Symbol("x", INT)

sys.add_clauses(
    {
        # init clause: inv(0)
        Clause(head=Apply(inv, [Int(0)])),
        # transition clause: inv(x) & -> inv(x + 1)
        Clause(body=Apply(inv, [x]), head=Apply(inv, [Plus(x, Int(1))])),
        # goal clause: inv(x) & x >= 5 -> FALSE
        Clause(body=And(Apply(inv, [x]), GE(x, Int(5))), head=FALSE()),
    }
)

# Create a Golem solver with OpenSMT as validator of SAT answers, and Carcara as validator of UNSAT proofs
print(
    "CHC solving with Golem. SAT result will be validated with OpenSMT, UNSAT proofs will be produced in LEGACY (uncheckable) format"
)
solver = golem.GolemSolver(
    smt_validator=opensmt.OpenSMTSolver(logic=QF_UFLIA),
    proof_format=ProofFormat.LEGACY
)
# Assign the system to the solver
solver.load_system(sys)
try:
    status = solver.solve(validate=True)
except PyCHCException as e:
    # Legacy proofs cannot be validated, so an exception is raised
    # Witness can still be extracted
    print(e)

print("Proof produced by Golem:")
print(solver.get_witness().serialize_to_string())

print("*" * 20)

# Let's now assign a proof checker to Golem, which also changes the produced proof format
solver.set_proof_checker(carcara.Carcara())
print("Re-solving the system with Golem, and validate UNSAT proofs with Carcara")
status = solver.solve(validate=True)

print("*" * 20)

## We can validate an externally provided witness on an externally provided system.

# Let's serialize the witness and system to files to simulate they are provided as external files.

# Serialize the CHC system to a file
sys_file = Path("chc_example2.smt2")
print(f"Serializing CHC system to {sys_file}")
sys.serialize(sys_file)

# Serialize the unsat proof to a file
witness_file = Path("unsat_proof.alethe")
print(f"Serializing UNSAT proof to {witness_file}")
solver.get_witness().serialize(witness_file)

print("*" * 20)

# Now, let's validate "unsat_proof.alethe" on "chc_example2.smt2"
print("Validating externally provided witness Carcara")
carcara.Carcara().validate_witness(
    witness=UnsatWitness.load_from_file(witness_file, ProofFormat.ALETHE),
    smt2file=sys_file
)

# Clean up
sys_file.unlink()
witness_file.unlink()