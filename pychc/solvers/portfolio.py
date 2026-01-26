# Portfolio solving
# Inspired by https://gist.github.com/Hook25/fc126773a0231d08fd434f7dfe41e9fd

import logging
import os
from pathlib import Path
import signal
from multiprocessing import Pool
from typing import Optional

from pychc.chc_system import CHCSystem
from pychc.solvers.chc_solver import CHCSolver
from pychc.solvers.witness import Status, Witness

from collections import namedtuple

TaskResult = namedtuple("TaskResult", ["id", "status", "raw_witness"])


# Helper: kill the process group
def kill_self(*args):
    os.killpg(os.getpgid(0), signal.SIGKILL)


# Helper: assign a process group to the pool handler
# When the handler is terminated, all child processes are killed
# This ensures to kill the forked solvers when the pool is closed
def initializer(*args):
    os.setpgid(0, 0)
    signal.signal(signal.SIGTERM, kill_self)


# Helper: run the pool on the given task.
# Store in the winning solver the raw output and status
def _run_pool(task, args, solvers):
    winner = None

    smt_validators = [solver.smt_validator for solver in solvers]
    if any(smt_validators):
        # cannot pickle solvers with attached SMT validators
        # temporarily unset them
        [solver.set_smt_validator(None) for solver in solvers]

    # Run the pool
    with Pool(initializer=initializer) as p:
        results: TaskResult = p.imap_unordered(task, args)
        for res in results:
            if res.status != Status.UNKNOWN:
                winner = res
                break
            logging.info(
                f"Solver {solvers[res.id].get_name()} returned UNKNOWN, discarding"
            )
    # Closing Pool kills all handlers and forked processes

    # Restore SMT validators
    if any(smt_validators):
        for solver, smt_validator in zip(solvers, smt_validators):
            solver.set_smt_validator(smt_validator)

    if winner:
        # Assign the raw output and status to the solver outside the process
        solver = solvers[winner.id]
        solver._status = winner.status
        solver._raw_output = winner.raw_witness
        logging.info(f"Solver {solver.get_name()} won returning {solver.get_status()}.")
    else:
        solver = None
        logging.info(f"No solver could solve the problem.")

    return solver


######


# Task distributed to each worker in solve_pool
def solve_task(solver_args: tuple[int, CHCSolver, CHCSystem, int]) -> TaskResult:
    id, solver, sys, timeout = solver_args
    solver.load_system(sys)
    status = solver.solve(timeout=timeout)
    return TaskResult(id, status, solver._raw_output)


def solve_pool(
    solvers: list[CHCSolver],
    sys: CHCSystem,
    timeout: Optional[int] = None,
) -> Optional[CHCSolver]:
    """
    Solve in parallel the given system with the solvers.
    Return the first solver that returns a conclusive result (SAT/UNSAT),
    or None if all return UNKNOWN or timeout.
    """

    # First, reset all solvers internal _system
    for solver in solvers: solver.load_system(None)

    args = ((id, solver, sys, timeout) for id, solver in enumerate(solvers))
    solver = _run_pool(solve_task, args, solvers)
    if solver:
        # make sure that the returned solver can be used
        # as if it solved the system directly
        solver.load_system(sys)
    return solver


# Task distributed to each worker in run_pool
def run_task(solver_args: tuple[int, CHCSolver, Path, int]) -> TaskResult:
    id, solver, file, timeout = solver_args
    status = solver.run(file, timeout=timeout)
    return TaskResult(id, status, solver._raw_output)


def run_pool(
    solvers: list[CHCSolver],
    file: Path,
    timeout: Optional[int] = None,
) -> Optional[CHCSolver]:
    """
    Run in parallel the given file with the solvers.
    Return the first solver that returns a conclusive result (SAT/UNSAT),
    or None if all return UNKNOWN or timeout.
    """

    args = ((id, solver, file, timeout) for id, solver in enumerate(solvers))
    return _run_pool(run_task, args, solvers)
