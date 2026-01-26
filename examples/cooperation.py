from pathlib import Path

from pychc.chc_system import CHCSystem

from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.golem import GolemSolver
from pychc.solvers.carcara import Carcara
from pychc.solvers.chc_solver import CHCSolver
from pychc.solvers.witness import ProofFormat
from pychc.shortcuts import Predicate, Apply, Clause

from pysmt.typing import INT
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import And, Symbol, Equals, Int, Plus, FALSE

import logging

logging.basicConfig(level=logging.DEBUG)

sys = CHCSystem(logic=QF_UFLIA)
inv = Predicate("inv", [INT])
sys.add_predicate(inv)
x = Symbol("x", INT)
nx = Symbol("nx", INT)
init_id = sys.add_clause(Clause(head=Apply(inv, [Int(0)])))
trans_id = sys.add_clause(
    Clause(
        body=And(
            Apply(inv, [x]),
            Equals(nx, Plus(x, Int(2))),
        ),
        head=Apply(inv, [nx]),
    )
)

# This system is SAT
# Finding the invariant needs to reason on parity, which Z3+GG can do
goal = Clause(body=And(Apply(inv, [x]), Equals(x, Int(1001))), head=FALSE())
goal_id = sys.add_clause(goal)

from pychc.solvers.portfolio import solve_pool, run_pool

solvers = [
    GolemSolver(proof_format=ProofFormat.ALETHE),
    Z3CHCSolver(global_guidance=True, name="Z3+GG"),
    Z3CHCSolver(global_guidance=False, name="Z3"),
    EldaricaSolver(name="eldarica"),
]

for solver in solvers:
    solver.set_smt_validator(CVC5Solver())

# Portfolio solving of sys
solver: CHCSolver = solve_pool(solvers, sys, timeout=30)
if solver:
    print(
        f"Portfolio selected solver: {solver.get_name()} with status: {solver.get_status()}"
    )
    solver.validate_witness(timeout=30)
else:
    print("Portfolio could not solve the problem")

# Make the sys UNSAT
# Since the cex is long, this should be solved by Golem first
sys.remove_clause(goal_id)
sys.add_clause(
    Clause(
        body=And(Apply(inv, [x]), Equals(x, Int(2000))),
        head=FALSE(),
    )
)
# Serialize the system to file to show that we can run the portfolio
# directly on an smt2 file
file = Path("_cooperation_example.smt2")
sys.serialize(file)

# Portfolio can be run directly on a given smt2 file
solver: CHCSolver = run_pool(solvers, file, timeout=30)
if solver:
    print(
        f"Portfolio selected solver: {solver.get_name()} with status: {solver.get_status()}"
    )
    # We did not load the system in the solver,
    # We can validate with Carcara directly on the input file.
    Carcara().validate_witness(solver.get_witness(), smt2file=file, timeout=30)
else:
    print("Portfolio could not solve the problem")
file.unlink()
