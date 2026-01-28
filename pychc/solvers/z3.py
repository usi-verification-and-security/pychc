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
        logic: Optional[Logic] = None,
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

    def _get_model(self) -> None:
        from pysmt.smtlib.script import SmtLibCommand
        import pysmt.smtlib.commands as smtcmd

        self._send_command(SmtLibCommand(smtcmd.GET_MODEL, []))

    def _run_and_read_output(
        self, sys_file: Path, timeout: Optional[int] = None, validate: bool = False
    ) -> Status:
        # This method overrides CHCSolver._run_and_read_output
        # because we need to interact with the solver process to ask
        # for a model/proof, instead of using command line flags.

        # This works for both run() and solve() methods
        # i.e, when running an input CHC system "as is" and trying to read the output,
        # or when running a loaded CHC system (serialized in system + check-sat).
        # At the end, we ensure to ask for a model/proof (if not already asked).

        # Spawn the SMT solver process
        SMTSolver.__init__(
            self,
            logic=QF_LRA,  # Dummy logic, overridden later
            binary_path=self._solver_path.parent,
            cmd_args=["-in"] + self.chc_options.to_array(),
        )

        logging.debug(f"Running {self.NAME}: " + " ".join(self.cmd_line))

        self.set_timeout(timeout)

        self._status = None
        self._raw_output = None

        try:
            from pychc.parser import scan_commands_in_smtlib_file

            for cmd in scan_commands_in_smtlib_file(sys_file):
                if cmd == "(exit)":
                    continue  # we will exit later
                self._send_raw_command(cmd)
                if cmd == "(get-model)" or cmd == "(get-proof)":
                    # wait for a possibly multi-line answer
                    self._raw_output = self._get_long_answer()
                    continue

                # read a single-line answer
                answer = self._get_answer()
                if "error" in answer.lower():
                    raise PyCHCSolverException(
                        f"{self.NAME} reported an error: {answer}"
                    )
                if answer not in {"success", "exit", "sat", "unsat", "unknown"}:
                    raise PyCHCSolverException(
                        f"Unexpected response from {self.NAME}: {answer}"
                    )
                if answer == "sat":
                    self._status = Status.SAT
                elif answer == "unsat":
                    self._status = Status.UNSAT
                elif answer == "unknown":
                    self._status = Status.UNKNOWN
            # all commands in file processed

            if not self._raw_output:
                # if no (get-model)/(get-proof) command was issued,
                # but we have a conclusive status,
                # we request the witness now
                if self._status == Status.SAT:
                    self._send_raw_command("(get-model)")
                    self._raw_output = self._get_long_answer()
                elif self._status == Status.UNSAT:
                    self._send_raw_command("(get-proof)")
                    self._raw_output = self._get_long_answer()

            # Finally, remove possible surrounding parentheses from SAT raw_output
            if self._status == Status.SAT and self._raw_output:
                self._raw_output = "\n".join(self._raw_output.splitlines()[1:-1])
            # quit the solver
            self.exit()

        except CalledProcessError as err:
            self._raw_output = (err.stdout or "") + (err.stderr or "")
            logging.error(f"{self.NAME} execution failed: {self._raw_output}")
            self._status = Status.UNKNOWN
            raise PyCHCSolverException(f"{self.NAME} execution failed")
        except TimeoutExpired as err:
            self.exit()
            logging.info(
                f"{self.NAME} execution timed out after {self.timeout} seconds"
            )
            self._status = Status.UNKNOWN
            return self._status

        if self._status != Status.UNKNOWN and validate:
            self.validate_witness()

        return self._status
