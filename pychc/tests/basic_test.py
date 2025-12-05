from pathlib import Path

from pychc.solvers.chc_solver import CHCStatus
from pychc.solvers.golem import GolemSolver
from pychc.chc_system import CHCSystem

from pysmt.typing import INT, BOOL, FunctionType
from pysmt.shortcuts import (
    Solver,
    And,
    Symbol,
    Function,
    Int,
    Implies,
    ForAll,
    Plus,
    FALSE,
    LT,
)

import logging

logging.basicConfig(level=logging.DEBUG)

sys = CHCSystem()

inv = Symbol("inv", FunctionType(BOOL, [INT]))
sys.add_predicate(inv)

sys.add_clause(Function(inv, [Int(0)]))

x = Symbol("x", INT)
nx = Symbol("nx", INT)

sys.add_clause(
    ForAll(
        [x],
        Implies(
            Function(inv, [x]),
            Function(inv, [Plus(x, Int(1))]),
        ),
    )
)
sys.add_clause(ForAll([x], Implies(And(Function(inv, [x]), LT(x, Int(0))), FALSE())))

tmp = Path("chc_example.smt2")
sys.serialize(tmp)

print("written to:", tmp.resolve())

# TODO: use a factory
# Note: this requires Golem to be installed and accessible in PATH
solver = GolemSolver(sys)

status = solver.solve(get_witness=True)
print(f"Solving status: {status}")

witness = solver.get_witness()

if status == CHCStatus.SAT:
    print("SAT witness definitions:")
    for var, expr in witness.definitions.items():
        print(f"{var} := {expr.function_body}")

    smt_solver = Solver(name="z3")
    queries = sys.get_validate_model_queries(witness)
    for query in queries:
        print(f"Validating query: {query}")
        if not smt_solver.is_valid(query):
            print("Query validation failed!")
        else:
            print("Query validated successfully.")
