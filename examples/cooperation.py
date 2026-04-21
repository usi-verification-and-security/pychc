from pathlib import Path
import time

from pychc.chc_system import CHCSystem
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.golem import GolemEngines, GolemSolver
from pychc.solvers.carcara import Carcara
from pychc.solvers.chc_solver import CHCSolver
from pychc.solvers.witness import ProofFormat, Status
from pychc.shortcuts import Predicate, Apply, Clause

from pychc.solvers.portfolio import solve_pool, run_pool

from pysmt.typing import INT
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import And, Not, Symbol, Equals, Int, Plus, FALSE

import logging

# Use DEBUG level to see each solver invocation in the portfolio
logging.basicConfig(level=logging.CRITICAL)

def make_next(var):
    return Symbol(f"next_{var.symbol_name()}", var.symbol_type())

if __name__ == "__main__":

    ## Model a CHC system

    # Simple transition system with a single int variable x
    # init: x = 0
    # trans: x' = x + 2
    x = Symbol("x", INT)
    init = Equals(x, Int(0))
    trans = Equals(make_next(x), Plus(x, Int(2)))

    # bad: x = 1001 (which is safe since x is always even)
    bad = Equals(x, Int(1001))


    # Create a CHC system from the above components.
    sys = CHCSystem(logic=QF_UFLIA)
    vars = list(init.get_free_variables())
    next_vars = list(map(make_next, vars))
    inv = Predicate("inv", [v.symbol_type() for v in vars])
    sys.add_predicate(inv)

    # init(x) -> inv(x)
    init_id = sys.add_clause(
        Clause(
            body=init,
            head=Apply(inv, vars)
        )
        )
    # inv(x) & trans(x, nx) -> inv(nx)
    trans_id = sys.add_clause(
        Clause(
            body=And(Apply(inv, vars), trans),
            head=Apply(inv, next_vars),
        )
    )
    # inv(x) & bad(x) -> FALSE
    property_id = sys.add_clause(
        Clause(
            body=And(Apply(inv, vars), bad),
            head=FALSE()
        )
    )

    print("Created a CHC system")
    print("Init: ", sys.get_clauses()[init_id].serialize())
    print("Trans: ", sys.get_clauses()[trans_id].serialize())
    print("Property: ", sys.get_clauses()[property_id].serialize())
    
    
    ## To solve the CHC system, create a pool of solvers
    print("\nLet's create a pool of solvers to solve the system in parallel with 30s timeout.")

    spacer = Z3CHCSolver(global_guidance=False, name="Z3")
    eldarica = EldaricaSolver(name="eldarica")
    # Note: we can have multiple instances of Golem with different backend engines
    golem_kind = GolemSolver(
        proof_format=ProofFormat.ALETHE, name="golem-Kind", engine=GolemEngines.kind
    )
    golem_tpa = GolemSolver(
        proof_format=ProofFormat.ALETHE, name="golem-TPA", engine=GolemEngines.tpa
    )

    start = time.time()
    solver: CHCSolver = solve_pool(
        [spacer, golem_tpa, golem_kind, eldarica], sys, timeout=30
    )
    assert solver is None, "In this tutorial, no solver should be able to solve the system within the timeout"
    print(">>> No solver could solve the system within the timeout")


    # Since the invariant needs to reason on parity, Z3+GG should be able to solve it.
    # Let's try again with Z3+GG included in the pool.
    print("\nNow, let's add Z3+GG to the pool and try again.")
    spacer_gg = Z3CHCSolver(global_guidance=True, name="Z3+GG")
    start = time.time()
    solver: CHCSolver = solve_pool(
        [spacer_gg, spacer, golem_tpa, golem_kind, eldarica], sys, timeout=30
    )
    print(f"Solver {solver.get_name()} solved first. Time taken: {round(time.time() - start, 3)}")
    assert solver.get_status() == Status.SAT


    # Check the witness validity (the system was loaded in the solver in `solve_pool`)
    # The following is equivalent to:
    #  solver.set_smt_validator(CVC5Solver())
    #  solver.validate_witness(timeout=30)
    sys.validate_sat_model(solver.get_witness(), CVC5Solver(), timeout=30)
    print(f"The witness returned by {solver.get_name()} has been validated by CVC5!")


    # Let's strengthen the transition relation with the learned invariant
    print("\nLet's see if we can leverage the witness returned by Z3+GG to help the other solvers solve the system faster.")
    new_clause_id = sys.strengthen_clause_with_witness(trans_id, solver.get_witness())
    print("A new clause was added to the system:")
    print(sys.get_clauses()[new_clause_id].serialize())
    

    # Let's see if the other solvers can solve the strengthened system now.
    print("Let's run the portfolio again without Z3+GG on the new system.")
    start = time.time()
    solver: CHCSolver = solve_pool(
        [spacer, golem_tpa, golem_kind, eldarica], sys, timeout=30
    )
    print(
        f"Solver {solver.get_name()} solved first on strengthened system. Time taken: {round(time.time() - start, 3)}"
    )
    assert solver.get_status() == Status.SAT


    # On the strengthened system, solving time was faster,
    # But let's make sure that the found model is valid for the original system
    print("\nLet's make sure that the found model is valid for the *original* system")
    # Remove the newly added clause to get back the original system
    sys.remove_clause(new_clause_id)
    sys.validate_sat_model(solver.get_witness(), CVC5Solver(), timeout=30)
    print("The witness is valid for the original system!")
    

    ##############################
    
    # Let's modify the system to create an UNSAT instance.

    print("\nNow, let's modify the property with a reachable one (i.e., the CHC system becomes UNSAT).")
    sys.remove_clause(property_id)
    # this new property is reachable
    new_bad = Equals(x, Int(2000))
    sys.add_clause(
        Clause(
            body=And(Apply(inv, vars), new_bad),
            head=FALSE(),
        )
    )
    
    # Serialize the system to file to show that we can run the portfolio
    # directly on an smt2 file, without loading it first in a CHCSystem.
    file = Path("_cooperation_example.smt2")
    sys.serialize(file)
    print(f"New system has been printed in {file}")
    
    # Run the solvers on the same smt2 file.
    # Since the cex is long, Golem TPA should be the first to solve it
    start = time.time()
    solver: CHCSolver = run_pool(
        [spacer_gg, spacer, golem_tpa, golem_kind, eldarica], file, timeout=30
    )
    print(
        f"Solver {solver.get_name()} solved first on UNSAT system. Time taken: {round(time.time() - start, 3)}"
    )
    if "golem" in solver.get_name():
        print("\nSince the winning solver supports proof generation, we can validate the returned proof with Carcara.")
        # We can validate with Carcara directly on the input file.
        Carcara().validate_witness(solver.get_witness(), smt2file=file, timeout=30)
        print("The witness is valid!")
    file.unlink()
