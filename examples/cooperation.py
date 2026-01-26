from pathlib import Path
import time

from pychc.chc_system import CHCSystem

from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.golem import GolemSolver
from pychc.solvers.carcara import Carcara
from pychc.solvers.chc_solver import CHCSolver
from pychc.solvers.witness import ProofFormat, Status
from pychc.shortcuts import Predicate, Apply, Clause

from pychc.solvers.portfolio import solve_pool, run_pool

from pysmt.typing import INT
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import And, Symbol, Equals, Int, Plus, FALSE

import logging

logging.basicConfig(level=logging.DEBUG)

# Create a CHC system
# inv(0)
# inv(x) -> inv(x + 2)
sys = CHCSystem(logic=QF_UFLIA)
inv = Predicate("inv", [INT])
sys.add_predicate(inv)
x, nx = Symbol("x", INT), Symbol("nx", INT)
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

# Check property: x != 1001
goal = Clause(body=And(Apply(inv, [x]), Equals(x, Int(1001))), head=FALSE())
goal_id = sys.add_clause(goal)


# Create a pool of solvers
spacer_gg = Z3CHCSolver(global_guidance=True, name="Z3+GG")
spacer = Z3CHCSolver(global_guidance=False, name="Z3")
golem = GolemSolver(proof_format=ProofFormat.ALETHE)
eldarica = EldaricaSolver(name="eldarica")

# Let's try to solve the system with all solvers in parallel.
# Since the invariant needs to reason on parity, Z3+GG should be the first to solve it,
start = time.time()
solver: CHCSolver = solve_pool([spacer_gg, spacer, golem, eldarica], sys, timeout=30)
print(f"Solver {solver.get_name()} solved first. Time taken: {time.time() - start}")
assert solver.get_status() == Status.SAT

# Check the witness validity (the system was loaded in the solver in `solve_pool`)
solver.set_smt_validator(CVC5Solver())
solver.validate_witness(timeout=30)
print("The witness is valid!")

##########

# Now, let's strengthen the transition relation with the learned invariant
new_trans_id = sys.strengthen_clause_with_witness(trans_id, solver.get_witness())
print("A new clause was added to the system:")
print(sys.get_clauses()[new_trans_id].serialize())

# Let's see if the other solvers can solve the strengthened system now.
start = time.time()
solver: CHCSolver = solve_pool([spacer, golem, eldarica], sys, timeout=30)
print(
    f"Solver {solver.get_name()} solved first on strengthened system. Time taken: {time.time() - start}"
)
assert solver.get_status() == Status.SAT

# On the strengthened system, solving time should be faster,
# but let's make sure that the found model is valid for the original system
sys.remove_clause(new_trans_id)
sys.validate_sat_model(solver.get_witness(), CVC5Solver(), timeout=30)
print("The witness is valid for the original system!")

##############################

# Let's modify the system to create an UNSAT instance.
sys.remove_clause(goal_id)
# New property: x != 2000
sys.add_clause(
    Clause(
        body=And(Apply(inv, [x]), Equals(x, Int(2000))),
        head=FALSE(),
    )
)

# Serialize the system to file to show that we can run the portfolio
# directly on an smt2 file, without loading it first in a CHCSystem.
file = Path("_cooperation_example.smt2")
sys.serialize(file)

# Run the solvers on the same smt2 file.
# Since the cex is long, Golem should be the first to solve it
start = time.time()
solver: CHCSolver = run_pool([spacer_gg, spacer, golem, eldarica], file, timeout=30)
print(
    f"Solver {solver.get_name()} solved first on UNSAT system. Time taken: {time.time() - start}"
)
if solver.get_name() == "golem":
    # We can validate with Carcara directly on the input file.
    Carcara().validate_witness(solver.get_witness(), smt2file=file, timeout=30)
    print("The UNSAT witness is valid!")
file.unlink()
