from pychc.exceptions import PyCHCInvalidResultException
from pychc.solvers import golem
from pychc.solvers.witness import Status, SatWitness
from pychc.solvers.golem import GolemSolver
from pychc.solvers.opensmt import OpenSMTSolver

from pychc.chc_system import CHCSystem

from pysmt.fnode import FNode
from pysmt.typing import INT, BOOL
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import (
    And,
    Or,
    Symbol,
    Equals,
    Int,
    Plus,
    Implies,
    Not,
    FALSE,
    LT,
    GE,
    reset_env,
)
from pychc.shortcuts import Predicate, Apply, Clause

import logging

logging.basicConfig(level=logging.DEBUG)


def k_liveness(
    xs: list[FNode], n_xs: list[FNode], init: FNode, trans: FNode, bad: FNode
):

    # Create a new K variable
    K, n_K = Symbol("K", INT), Symbol("n_K", INT)
    xs.append(K)
    n_xs.append(n_K)

    # Create an "inv" predicate
    inv = Predicate("kliv_inv", [INT] * len(xs))
    # init & k = 0 -> inv(xs)
    init_clause = Clause(And(init, Equals(K, Int(0))), Apply(inv, xs))
    # trans & inv(xs) & (bad -> K' = K + 1) & (!bad -> K' = K) -> inv(xs')
    trans_clause = Clause(
        And(
            trans,
            Apply(inv, xs),
            Implies(bad, Equals(n_K, Plus(K, Int(1)))),
            Implies(Not(bad), Equals(n_K, K)),
        ),
        Apply(inv, n_xs),
    )
    # Create a CHC system
    sys = CHCSystem(logic=QF_UFLIA)
    sys.add_predicate(inv)
    sys.add_clauses({init_clause, trans_clause})

    solver = GolemSolver()
    K_value = 1
    while True:
        # goal: inv(xs) -> K < K_value
        goal = Clause(Apply(inv, xs), LT(K, Int(K_value)))
        idx = sys.add_clause(goal)
        solver.load_system(sys)
        status = solver.solve(timeout=2)
        if status == Status.SAT:
            try:
                # validate only when SAT answer
                sys.validate_sat_model(
                    solver.get_witness(), OpenSMTSolver(logic=QF_UFLIA)
                )
                # bad can be visited at least K_value times
                print("Property FG !bad is valid.")
                return Status.SAT
            except PyCHCInvalidResultException as e:
                print(e)
                pass

        sys.remove_clause(idx)
        K_value += 1
        if K_value > 10:
            print("Giving up after 10 iterations")
            return Status.UNKNOWN


def liveness2safety(
    xs: list[FNode], nextxs: list[FNode], init: FNode, trans: FNode, bad: FNode
):
    print("Liveness-to-safety transformation")

    flag, next_flag = Symbol("flag", BOOL), Symbol("next_flag", BOOL)

    copys = [Symbol(f"copy_{x.symbol_name()}", x.get_type()) for x in xs]
    nextcopys = [Symbol(f"copy_{nx.symbol_name()}", nx.get_type()) for nx in nextxs]

    new_xs = xs + [flag] + copys
    new_nextxs = nextxs + [next_flag] + nextcopys

    new_init = And(init, Not(flag))
    new_trans = And(
        trans,
        Implies(flag, next_flag),
        Implies(
            And(bad, Not(flag)), And(Equals(x, nc) for x, nc in zip(new_xs, nextcopys))
        ),
        Implies(
            Or(Not(bad), flag), And(Equals(c, nc) for c, nc in zip(copys, nextcopys))
        ),
    )
    goal = And(flag, And(Equals(x, c) for x, c in zip(xs, copys)))

    sys = CHCSystem(logic=QF_UFLIA)
    inv = Predicate("l2sinv", [x.get_type() for x in new_xs])
    sys.add_predicate(inv)
    sys.add_clause(Clause(new_init, Apply(inv, new_xs)))
    sys.add_clause(Clause(And(new_trans, Apply(inv, new_xs)), Apply(inv, new_nextxs)))
    sys.add_clause(Clause(Apply(inv, new_xs), Not(goal)))

    solver = GolemSolver()
    solver.set_unsat_proof_format(golem.ProofFormat.LEGACY)
    solver.load_system(sys)
    status = solver.solve(timeout=2)
    print(f"Liveness-to-safety solving status: {status}")
    if status == Status.UNSAT:
        print("Property FG !bad is false.")
        print("Found lasso-shaped path satisfying GF bad")
        witness = solver.get_witness()
        print(witness.text)
    elif status == Status.SAT:
        print("Property FG !bad may be valid. No lasso-shaped path found.")
    else:
        print("liveness2safety: UNKNOWN")


x = Symbol("x", INT)
nx = Symbol("nx", INT)
init = Equals(x, Int(0))
trans = And(
    Implies(LT(x, Int(10)), Equals(nx, Plus(x, Int(1)))),
    Implies(GE(x, Int(10)), Equals(nx, Int(5))),
)
bad = LT(x, Int(3))
k_liveness([x], [nx], init, trans, bad)
liveness2safety([x], [nx], init, trans, bad)

print("---- NEW SYSTEM ----")
reset_env()

x = Symbol("x", INT)
nx = Symbol("nx", INT)
init = Equals(x, Int(0))
trans = And(
    Implies(LT(x, Int(10)), Equals(nx, Plus(x, Int(1)))),
    Implies(GE(x, Int(10)), Equals(nx, Int(5))),
)
bad = LT(x, Int(6))
k_liveness([x], [nx], init, trans, bad)
liveness2safety([x], [nx], init, trans, bad)
