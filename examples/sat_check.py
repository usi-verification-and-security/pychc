from pathlib import Path

from pychc.solvers.witness import Status
from pychc.solvers.golem import GolemSolver
from pychc.solvers.opensmt import OpenSMTSolver
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
status = solver.solve(get_witness=True)
print(f"Solving status: {status}")

witness = solver.get_witness()

assert status == Status.SAT and witness is not None

print("SAT witness definitions:")
for var, expr in witness.definitions.items():
    print(f"{var} := {expr.function_body}")

# Validate the witness with an external SMT solver
queries = sys.get_validate_model_queries(witness)

smt_solver = OpenSMTSolver(logic=QF_UFLIA)
for query in queries:
    print(f"Validating query: {query}")
    if not smt_solver.is_valid(query):
        print("ERROR! Query validation failed!")
    else:
        print("Query validated successfully.")
        print(smt_solver.get_proof())
