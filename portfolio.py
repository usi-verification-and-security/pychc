from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.solvers.golem import GolemSolver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.chc_system import CHCSystem
from pychc.solvers.witness import Status

from multiprocessing import Process, SimpleQueue
import os
import signal

def task(id, solver : CHCSolver, chc_system : CHCSystem, timeout, queue):
    os.setpgid(0,0)
    solver.load_system(chc_system)
    res = solver.solve(timeout)
    queue.put((id, res))


def portfolio_solve(solvers : list[CHCSolver], chc_system : CHCSystem, timeout):
    res_queue = SimpleQueue()
    ps = [Process(target=task, args=(id, solver,chc_system, timeout, res_queue), daemon=True) for (id, solver) in enumerate(solvers)]
    try:
        for p in ps:
            p.start()
        
        unknowns = 0
        while unknowns < len(solvers):
            (id, res) = res_queue.get()
            if res != Status.UNKNOWN:
                break
            else:
                unknowns = unknowns + 1
    finally:
        for p in ps:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGTERM)
            except ProcessLookupError:
                pass
    return (res, solvers[id].NAME)

if __name__ == "__main__":
    solvers = [GolemSolver(), Z3CHCSolver(), EldaricaSolver()]
    # solvers = [GolemSolver(), EldaricaSolver()]
    # solvers = [Z3CHCSolver()]
    system = CHCSystem.load_from_smtlib("long.smt2")
    timeout = 15
    output = portfolio_solve(solvers, system, timeout)
    print(output)
