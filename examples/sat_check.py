from pathlib import Path

from pychc.solvers.chc_solver import CHCStatus
from pychc.solvers.golem import GolemSolver
from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCSolverException

from pysmt.typing import INT, BOOL, FunctionType
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import (
    Solver,
    And,
    Symbol,
    Equals,
    Int,
    Plus,
    FALSE,
    LT,
)
from pychc.shortcuts import Predicate, Apply

import logging

logging.basicConfig(level=logging.DEBUG)

sys = CHCSystem(logic=QF_UFLIA)

# Create a predicate inv(x: Int)
inv = Predicate("inv", [INT])
sys.add_predicate(inv)

sys.add_clause(head=Apply(inv, [Int(0)]))

x = Symbol("x", INT)
nx = Symbol("nx", INT)

sys.add_clause(
    body=And(Apply(inv, [x]), Equals(nx, Plus(x, Int(1)))),
    head=Apply(inv, [nx])
)
sys.add_clause(
    body=And(Apply(inv, [x]), LT(x, Int(0))),
    head=FALSE()
)

# Serialize the CHC system to an SMT-LIBv2 file
tmp = Path("chc_example.smt2")
sys.serialize(tmp)
print("written to:", tmp.resolve())

# TODO: use a factory
# Note: this requires Golem to be installed and accessible in PATH
# otherwise, set `binary_path` argument to the GolemSolver constructor
solver = GolemSolver(sys)
status = solver.solve(get_witness=True)
print(f"Solving status: {status}")

witness = solver.get_witness()

if status == CHCStatus.SAT:
    print("SAT witness definitions:")
    for var, expr in witness.definitions.items():
        print(f"{var} := {expr.function_body}")

    # Validate the witness with an external SMT solver
    queries = sys.get_validate_model_queries(witness)
    smt_solver = Solver(name="z3")
    for query in queries:
        print(f"Validating query: {query}")
        if not smt_solver.is_valid(query):
            print("ERROR! Query validation failed!")
        else:
            print("Query validated successfully.")
else:
    raise PyCHCSolverException("The provided CHC system should be SAT")