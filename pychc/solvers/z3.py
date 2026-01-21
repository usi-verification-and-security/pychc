from __future__ import annotations

import logging
from pathlib import Path
from typing import Optional
from subprocess import CalledProcessError, TimeoutExpired

from pysmt.logics import (
    Logic,
    QF_LRA,
    QF_LIA,
    QF_LIRA,
    QF_UFLIA,
    QF_UFLRA,
    LIA,
    LRA,
    UFLIRA,
)
from pysmt.shortcuts import get_env

from pychc.solvers.witness import ProofFormat, Status
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions
from pychc.exceptions import PyCHCSolverException


class Z3SMTOptions(SMTSolverOptions):
    """
    Options for Z3 SMT solver.
    """

    PROOF_FORMATS = set()

    def __call__(self, solver):
        # Base options (including produce-proofs)
        super().__call__(solver)
        solver.set_option(":produce-proofs", "true")


class Z3SMTSolver(SMTSolver):
    """Z3 SMT solver adapter using SMT-LIB textual interface."""

    NAME = "z3"
    LOGICS = (QF_LRA, QF_LIA, QF_LIRA, QF_UFLIA, QF_UFLRA, LIA, LRA, UFLIRA)
    OptionsClass = Z3SMTOptions

    def __init__(
        self,
        logic: Logic,
        binary_path: Optional[Path] = None,
        **options,
    ):
        super().__init__(
            logic=logic, binary_path=binary_path, cmd_args=["-in"], **options
        )


class Z3CHCOptions(CHCSolverOptions):
    """Options passed to the Z3 process via command line flags."""

    def __init__(self, **base_options):
        super().__init__(**base_options)

    def use_global_guidance(self, enable: bool = True) -> None:
        self._set_flag("fp.spacer.global=true", enable)

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        """Enable certificate printing"""
        if value and proof_format:
            raise PyCHCSolverException("Z3 does not support custom proof formats.")
        # We prefer not to use fp.print_certificate flag because
        # it prints models in a different format than other solvers.
        # Instead, we add (get-model) command if (check-sat) returns SAT.
        # Similarly, (get-proof) command if (check-sat) returns UNSAT.
        ###  self._set_flag("fp.print_certificate=true", value)
        pass


class Z3CHCSolver(CHCSolver, SMTSolver):
    """Solver adapter for the Z3 CHC solver."""

    NAME = "z3"
    OPTION_CLASS = Z3CHCOptions
    LOGICS = (QF_LRA, QF_LIA, QF_LIRA, QF_UFLIA, QF_UFLRA, LIA, LRA, UFLIRA)

    # OptionClass used by SMTSolver
    OptionsClass = Z3SMTOptions

    def __init__(self, global_guidance: bool = False, **args):
        CHCSolver.__init__(self, **args)
        if global_guidance:
            self.chc_options.use_global_guidance(True)

    def set_logic(self, dummy_logic):
        # do nothing, logic is set via input file
        pass

    def _send_raw_command(self, cmd: str, timeout: Optional[int] = None) -> str:
        """Send a raw text command to the solver."""
        self._debug("Sending raw command: %s", cmd)
        self.commands[-1].append(cmd)
        self.solver_stdin.write(cmd + "\n")
        self.solver_stdin.flush()
        res = self._get_answer(timeout=timeout)
        if res not in {"success", "sat", "unsat", "unknown"}:
            raise PyCHCSolverException(f"Unexpected response from {self.NAME}: {res}")
        return res

    def _get_answer(self, timeout: Optional[int] = None) -> str:
        """Reads a line from STDOUT pipe"""
        if timeout is None:
            res = self.solver_stdout.readline().strip()
        else:
            import select

            out, _, _ = select.select([self.solver_stdout], [], [], timeout)
            if out:
                res = self.solver_stdout.readline().strip()
            else:
                raise TimeoutExpired(cmd=self.NAME, timeout=timeout)
        self._debug("Read: %s", res)
        return res

    def _get_model(self) -> None:
        from pysmt.smtlib.script import SmtLibCommand
        import pysmt.smtlib.commands as smtcmd

        self._send_command(SmtLibCommand(smtcmd.GET_MODEL, []))

    def solve(self, validate: bool = False, timeout: Optional[int] = None) -> Status:
        if not self.system:
            raise PyCHCSolverException("No CHC system loaded in solver")

        # Spawn the SMT solver process
        SMTSolver.__init__(
            self,
            logic=QF_LRA,  # Dummy logic, overridden later
            binary_path=self._solver_path.parent,
            cmd_args=["-in"] + self.chc_options.to_array(),
            solver_options={"debug_interaction": True},
        )

        # Always ask for a witness.
        expected_validation = True  # self.smt_validator or self.proof_format

        input_file = self.get_input_file()

        try:
            res = None

            # assuming that sending raw commands is not considered part of the timeout
            for i, line in enumerate(input_file.read_text().splitlines()):
                if line.strip():
                    res = self._send_raw_command(line, timeout=timeout)

            if res == "sat":
                self._status = Status.SAT
                if expected_validation:
                    # send command (get-model)
                    self._get_model()
                    raw_output = self._get_long_answer()
                    self._raw_output = "\n".join(raw_output.splitlines()[1:-1])

            elif res == "unsat":
                self._status = Status.UNSAT
                if expected_validation:
                    # send command (get-proof)
                    self._send_command_get_proof()
                    self._raw_output = self._get_long_answer()
            else:
                self._status = Status.UNKNOWN

            # quit the solver
            self.exit()

        except CalledProcessError as err:
            self._raw_output = (err.stdout or "") + (err.stderr or "")
            logging.error(f"{self.NAME} execution failed: {self._raw_output}")
            self._status = Status.UNKNOWN
            raise PyCHCSolverException(f"{self.NAME} execution failed")
        except TimeoutExpired as err:
            logging.error(f"{self.NAME} execution timed out after {timeout} seconds")
            self._status = Status.UNKNOWN
            return self._status

        if self._status != Status.UNKNOWN and validate:
            self.validate_witness()

        return self._status
