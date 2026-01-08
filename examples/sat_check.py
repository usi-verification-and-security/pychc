from pathlib import Path

from pychc.solvers.witness import Status, SatWitness
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.golem import GolemSolver
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.opensmt import OpenSMTSolver
from pychc.solvers.carcara import Carcara

from pychc.chc_system import CHCSystem

from pysmt.typing import INT, REAL
from pysmt.logics import QF_UFLRA, QF_UFLIA
from pysmt.shortcuts import (
    And,
    Symbol,
    Equals,
    Int, Real,
    Plus, Minus,
    FALSE,
    LT,
)
from pychc.shortcuts import Predicate, Apply, Clause

import logging

logging.basicConfig(level=logging.DEBUG)

sys = CHCSystem(logic=QF_UFLIA)

# Create a predicate inv(x: Int)
inv = Predicate("inv", [INT])
sys.add_predicate(inv)

sys.add_clause(Clause(Apply(inv, [Int(0)])))

x = Symbol("x", INT)
nx = Symbol("nx", INT)

sys.add_clause(Clause(
    body=And(Apply(inv, [x]), Equals(nx, Plus(x, Int(1)))),
    head=Apply(inv, [nx])
))
sys.add_clause(Clause(
    body=And(Apply(inv, [x]), LT(x, Int(0))),
    head=FALSE()
))

# Serialize the CHC system to an SMT-LIBv2 file
tmp = Path("chc_example.smt2")
sys.serialize(tmp)
print("written to:", tmp.resolve())

# Re-read the CHC system from the SMT-LIBv2 file
sys = CHCSystem.load_from_smtlib(tmp)

tmp = Path("chc_example2.smt2")
sys.serialize(tmp)
print("written to:", tmp.resolve())

# TODO: use a factory
# Note: this requires Golem to be installed and accessible in PATH
# otherwise, set `binary_path` argument to the GolemSolver constructor
solver = GolemSolver()
solver.load_system(sys)

smt_validator = OpenSMTSolver(logic=QF_UFLIA)
solver.set_smt_validator(smt_validator)

status = solver.solve(validate=False)
print(f"Solving status: {status}")

solver.validate_witness()

witness = solver.get_witness()

assert status == Status.SAT and witness is not None

print("SAT witness definitions:")
for var, expr in witness.definitions.items():
    print(f"{var} := {expr.function_body}")

sat_witness = Path("sat_witness.smt2")
print(f"Serializing SAT witness to {sat_witness}")
witness.serialize(sat_witness)

print("Validating re-read SAT witness")
witness2 = SatWitness.load_from_file(sat_witness)
smt_validator2 = CVC5Solver(logic=QF_UFLIA, proof_checker=Carcara())
sys.validate_sat_model(witness2, smt_validator2)

clauses = sys.learn_from_witness(witness)
print("Learnt clauses:")
for clause in clauses:
    print(clause)

tmp = Path("chc_example2.smt2")
sys.serialize(tmp)
print("new system written to:", tmp.resolve())

solver = Z3CHCSolver()
solver.load_system(sys)
solver.solve()