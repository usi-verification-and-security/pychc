from pychc.exceptions import PyCHCInvalidResultException
from pychc.solvers import golem
from pychc.solvers.witness import Status
from pychc.solvers.golem import GolemSolver
from pychc.solvers.opensmt import OpenSMTSolver

from pychc.chc_system import CHCSystem

from pysmt.fnode import FNode
from pysmt.typing import INT, BOOL
from pysmt.logics import QF_UFLIA
from pysmt.shortcuts import (
    FALSE, Symbol,
    And, Or, Not, Implies,
    Equals, Int, Plus, LT, GE
)
from pychc.shortcuts import Predicate, Apply, Clause

import logging
logging.basicConfig(level=logging.CRITICAL)

def make_next(var):
    return Symbol(f"next_{var.symbol_name()}", var.symbol_type())

def create_chc_system(vars, init, trans, inv_name="inv"):
    sys = CHCSystem(logic=QF_UFLIA)
    next_vars = list(map(make_next, vars))
    inv = Predicate(inv_name, [v.symbol_type() for v in vars])
    sys.add_predicate(inv)
    # init(x) -> inv(x)
    sys.add_clause(
        Clause(
            body=init,
            head=Apply(inv, vars)
        )
        )
    # inv(x) & trans(x, nx) -> inv(nx)
    sys.add_clause(
        Clause(
            body=And(Apply(inv, vars), trans),
            head=Apply(inv, next_vars),
        )
    )
    return sys, inv


def k_liveness(xs: list[FNode], init: FNode, trans: FNode, bad: FNode):

    print("\n>>> K-liveness transformation")

    # Create a new K variable
    K = Symbol("K", INT)
    
    # update init and trans with K variable
    init = And(init, Equals(K, Int(0)))
    trans = And(
        trans,
        Implies(bad, Equals(make_next(K), Plus(K, Int(1)))),
        Implies(Not(bad), Equals(make_next(K), K)),
    )
    xs.append(K)

    sys, inv = create_chc_system(xs, init, trans, inv_name="kliveness_inv")

    # print("Created CHC system:")
    # for clause in sys.get_clauses():
    #     print(clause.serialize())

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
                print(f"Hurray! Golem said that `bad` cannot be reached more than {K_value} times.")
                print("Let's validate the returned invariant with OpenSMT to be sure.")
                # validate only when SAT answer
                sys.validate_sat_model(
                    solver.get_witness(), OpenSMTSolver(logic=QF_UFLIA)
                )
                # bad can be visited at least K_value times
                print(">> K-Liveness proved that FG !bad is true.")
                return Status.SAT
            except PyCHCInvalidResultException as e:
                print(e)
                pass

        print(f"... Golem could not prove that `bad` cannot be reached more than {K_value} times.")
        sys.remove_clause(idx)
        K_value += 1
        if K_value > 10:
            print("Giving up after 10 iterations. The property may be valid, but we cannot conclude with K-Liveness.")
            return Status.UNKNOWN


def liveness2safety(xs: list[FNode], init: FNode, trans: FNode, bad: FNode):
    print("\n>>> Liveness-to-safety transformation")

    flag = Symbol("flag", BOOL)
    next_flag = make_next(flag)

    def make_copy(x):
        return Symbol(f"copy_{x.symbol_name()}", x.get_type())
    
    init = And(init, Not(flag))
    trans = And(
        trans, 
        Implies(flag, next_flag),
        Implies(And(bad, Not(flag)), And(Equals(x, make_next(make_copy(x))) for x in xs)),
        Implies(Or(Not(bad), flag), And(Equals(make_copy(x), make_next(make_copy(x))) for x in xs)),
    )

    all_vs = xs + [flag] + [make_copy(x) for x in xs]
    sys, inv = create_chc_system(all_vs, init, trans, inv_name="liveness2safety_inv")

    goal = And(flag, And(Equals(x, make_copy(x)) for x in xs))
    sys.add_clause(
        Clause(
            body=And(Apply(inv, all_vs), goal),
            head=FALSE(),
        )
    )

    # print("Created CHC system:")
    # for clause in sys.get_clauses():
    #     print(clause.serialize())

    print("Looking for a lasso-shaped path satisfying GF bad with Golem...")
    solver = GolemSolver()
    solver.set_unsat_proof_format(golem.ProofFormat.LEGACY)
    solver.load_system(sys)
    status = solver.solve(timeout=2)
    if status == Status.UNSAT:
        print("Property FG !bad is false.")
        print("Golem found lasso-shaped path satisfying GF bad")
        witness = solver.get_witness()
        print(witness.text)
    elif status == Status.SAT:
        print("Property FG !bad may be valid. No lasso-shaped path found.")
    else:
        print("Golem returned UNKNOWN.")


def get_system():
    # transition system whose execution is:
    # 0 -> 1 -> 2 -> 3 -> 4 -> 5 -> 6 -> 7 -> 8 -> 9 -> 10 -> 5 -> ...
    x = Symbol("x", INT)
    init = Equals(x, Int(0))
    trans = And(
        Implies(LT(x, Int(10)), Equals(make_next(x), Plus(x, Int(1)))),
        Implies(GE(x, Int(10)), Equals(make_next(x), Int(5))),
    )
    print("Transition system:")
    print("Init: ", init.serialize())
    print("Trans: ", trans.serialize())
    return x, init, trans


if __name__ == "__main__":

    x, init, trans = get_system()
    print("\nLet's check property: FG x >= 3: expected to be true.")
    bad = LT(x, Int(3))
    k_liveness([x], init, trans, bad)
    liveness2safety([x], init, trans, bad)

    print("*" * 40)
    print("\nLet's check property: FG x >= 6: expected to be false, because x = 5 is visited infinitely often.")
    bad = LT(x, Int(6))
    k_liveness([x], init, trans, bad)
    liveness2safety([x], init, trans, bad)
