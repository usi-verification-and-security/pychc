from __future__ import annotations

from subprocess import TimeoutExpired
import tempfile

from io import StringIO
from pathlib import Path
from select import select
from shutil import which

from time import time
from typing import Optional

from pysmt.smtlib.solver import SmtLibSolver, SmtLibOptions
from pysmt.environment import get_env
from pysmt.logics import Logic

from pychc.solvers.witness import ProofFormat, Status, Status
from pychc.solvers.proof_checker import ProofChecker
from pychc.exceptions import (
    PyCHCInvalidResultException,
    PyCHCSolverException,
    PyCHCInternalException,
)


class SMTSolverOptions(SmtLibOptions):
    """
    Options for SMTSolver extending pySMT's SmtLibOptions with proof support.

    Adds:
    - produce_proofs: when True sets `:produce-proofs` to `true`.
    - Additional `solver_options` passed through as standard SMT-LIB `set-option`.
    """

    PROOF_FORMATS: set[ProofFormat] = set()

    def __init__(self, **base_options):
        super().__init__(**base_options)
        self.produce_proofs: bool = False
        self.proof_format: Optional[ProofFormat] = None

    def set_produce_proofs(
        self, enable: bool = True, proof_format: Optional[ProofFormat] = None
    ) -> None:
        self.produce_proofs = enable
        if enable:
            if proof_format not in self.PROOF_FORMATS:
                raise PyCHCSolverException(
                    f"Unsupported proof format for solver: {proof_format}"
                )
            self.proof_format = proof_format
        else:
            self.proof_format = None

    def set_proof_format(self, proof_format: ProofFormat) -> None:
        self.proof_format = proof_format

    def __call__(self, solver: SmtLibSolver):
        # Invoke base options first
        super().__call__(solver)
        # Enable proofs if requested
        if self.produce_proofs:
            solver.set_option(":produce-proofs", "true")


class SMTSolver(SmtLibSolver):
    """
    Abstract SMT solver interface using SMT-LIB textual protocol.

    Inherits from pySMT's SmtLibSolver and adds `get_proof()` support.
    Implementations can override NAME/LOGICS and provide additional options.
    """

    NAME: str = ""
    LOGICS = set()
    OptionsClass = SMTSolverOptions

    def __init__(
        self,
        logic: Optional[Logic] = None,
        binary_path: Optional[Path] = None,
        cmd_args: Optional[list[str]] = None,
        proof_checker: Optional[ProofChecker] = None,
        **options,
    ):
        # Locate solver binary
        if not self.NAME:
            raise PyCHCInternalException("SMTSolver.NAME must be defined by subclass")
        solver_path = which(self.NAME, path=str(binary_path) if binary_path else None)
        if not solver_path:
            raise PyCHCSolverException(f"Executable for {self.NAME} not found")
        self._solver_path = Path(solver_path)
        if not self._solver_path.is_file():
            raise PyCHCSolverException(
                f"Executable for {self.NAME} not found at: {self._solver_path}"
            )

        if logic:
            if not any(logic <= l for l in self.LOGICS):
                raise PyCHCSolverException(
                    f"Logic {logic} not supported by solver {self.NAME}"
                )
            # Try to upgrade to quantified logic, if supported
            q_logic = logic.get_quantified_version()
            if any(q_logic <= l for l in self.LOGICS):
                logic = q_logic
        self.logic = logic

        self.proof_checker = proof_checker

        # Needed to track relevant commands for proof checking
        self.commands = [[]]

        # Timeout for each read operation
        self.timeout: Optional[int] = None

        self.cmd_line = [str(self._solver_path)] + (cmd_args if cmd_args else [])
        self._extra_options = options

        self.recreate_process()

    def recreate_process(self) -> None:
        # Create an interactive subprocess with the solver binary
        env = get_env()
        # super() needs a logic. we use a dummy one if none is provided
        dummy_logic = self.logic if self.logic else next(iter(self.LOGICS), None)
        self._do_not_set_logic = self.logic is None
        super().__init__(
            args=self.cmd_line,
            environment=env,
            logic=dummy_logic,
            LOGICS=self.LOGICS,
            **self._extra_options,
        )
        # restore logic to None  if it was not provided
        if self._do_not_set_logic:
            self.logic = None
        self._do_not_set_logic = False

        self._status = None
        self._proof = None
        self.smt2file = None
        self.proof_file = None

        self._set_proof_checker_option()

    def set_logic(self, logic: Logic) -> None:
        if self._do_not_set_logic:
            return
        if not any(logic <= l for l in self.LOGICS):
            raise PyCHCSolverException(
                f"Logic {logic} not supported by solver {self.NAME}"
            )
        super().set_logic(logic)
        self.logic = logic

    def get_logic(self) -> Logic:
        return self.logic

    def set_timeout(self, timeout: Optional[int]) -> None:
        self.timeout = timeout

    def set_proof_checker(self, proof_checker: Optional[ProofChecker]) -> None:
        """
        Set or change the proof checker used for validating proofs.
        """
        self.proof_checker = proof_checker

    def _set_proof_checker_option(self) -> None:
        if self.proof_checker is None:
            self.options.set_produce_proofs(False)
        else:
            self.options.set_produce_proofs(True, self.proof_checker.get_proof_format())
        self.options(self)

    def get_proof_format(self) -> Optional[ProofFormat]:
        if self.proof_checker:
            return self.proof_checker.get_proof_format()
        return None

    def _send_command_get_proof(self):
        # NOTE: Workaround to the lack of GET_PROOF serialization in pySMT
        # The following is mocking:
        #     self._send_command(SmtLibCommand(smtcmd.GET_PROOF, []))
        # Avoids adding this command to `self.commands`
        self._debug(f"Sending: (get-proof)")
        self.solver_stdin.write(f"(get-proof)\n")
        self.solver_stdin.flush()

    def _send_command(self, cmd):
        """Sends a command to the STDIN pipe."""
        string_io = StringIO()
        cmd.serialize(string_io, daggify=True)
        val = string_io.getvalue()
        self._send_raw_command(val.strip())

    def reset_assertions(self):
        super().reset_assertions()
        self.delete_files()
        self.commands = [[]]

    def push(self):
        super().push()
        self.commands.append([])

    def pop(self):
        super().pop()
        self.delete_files()
        self.commands.pop(-1)

    def get_proof(self) -> str:
        """
        Request a proof/certificate from the solver using `(get-proof)`.
        """
        self._send_command_get_proof()
        self._proof = self._get_long_answer()
        return self._proof

    def delete_files(self) -> None:
        try:
            self.smt2file.unlink()
            self.proof_file.unlink()
        except Exception:
            pass

    def get_smt2_file(self) -> Path:
        # serialize active smt2 commands
        self.smt2file = Path(tempfile.NamedTemporaryFile(suffix=".smt2").name)
        with open(self.smt2file, "w") as pf:
            pf.write("\n".join(c for stack in self.commands for c in stack))
        return self.smt2file

    def get_proof_file(self) -> Path:
        proof = self.get_proof()
        self.proof_file = Path(tempfile.NamedTemporaryFile(suffix=".proof").name)
        # serialize proof
        with open(self.proof_file, "w") as prf:
            prf.write(proof)
        return self.proof_file

    def validate_proof(self):
        """
        Request a proof from the solver and validate it using the configured proof checker
        """
        if not self.proof_checker:
            raise PyCHCSolverException(
                f"Cannot validate proof: no proof checker configured for solver {self.NAME}"
            )
        self.get_proof_file()
        self.get_smt2_file()
        ok = self.proof_checker.validate(self.proof_file, self.smt2file)
        if not ok:
            raise PyCHCInvalidResultException(
                f"SMT solver {SMTSolver.NAME} produced an invalid proof. See proof file: {self.get_proof_file()} for query {self.get_smt2_file()}"
            )
        self.delete_files()

    def _get_long_answer(self) -> str:
        # Read all currently available output:
        # Block until the first data chunk arrives (or max timeout elapses)
        # After first data, switch to idle-timeout mode to detect completion
        # Enforce a hard max timeout of 10s for the entire read
        buf: list[str] = []
        err_str: list[str] = []
        start = time()
        idle_timeout = 1  # seconds to wait for more data after first chunk
        max_timeout = 20.0  # hard cap for overall read

        fd = self.solver.stdout  # raw buffered reader from Popen
        fe = self.solver.stderr  # raw buffered reader from Popen
        parenthesis = 0

        while True:
            remaining = max_timeout - (time() - start)
            if remaining <= 0:
                break

            # Before first chunk: wait up to remaining time (blocking)
            # After first chunk: wait only idle_timeout (bounded by remaining)
            wait = remaining if parenthesis == 0 else min(idle_timeout, remaining)
            rlist, _, _ = select([fd, fe], [], [], wait)
            if rlist:
                if fe in rlist:
                    # Read all from stderr and log
                    chunk = fe.read1(8192)
                    if not chunk:
                        break
                    err_str.append(chunk.decode("utf-8", errors="replace").strip())
                if fd in rlist:
                    chunk = fd.read1(8192)
                    if not chunk:
                        break
                    chunk_str = chunk.decode("utf-8", errors="replace")
                    buf.append(chunk_str)
                    parenthesis += chunk_str.count("(") - chunk_str.count(")")
                continue
            else:
                # No data arrived within the wait window
                if parenthesis == 0:
                    # Consider stream idle -> done
                    break
                # Otherwise, keep waiting until max_timeout expires
                continue
        if err_str:
            raise PyCHCSolverException(
                f"{self.NAME} reported an error: {''.join(err_str)}"
            )
        proof = "".join(buf).strip()
        self._debug("Read proof bytes: %d", len(proof))
        return proof

    def _send_raw_command(self, cmd: str):
        """Send a raw text command to the solver."""
        self._debug("Sending raw command: %s", cmd)
        self.commands[-1].append(cmd)
        self.solver_stdin.write(cmd + "\n")
        self.solver_stdin.flush()

    def _get_answer(self) -> str:
        """Reads a line from STDOUT pipe"""
        if self.timeout is None:
            res = self.solver_stdout.readline().strip()
        else:
            import select

            out, _, _ = select.select([self.solver_stdout], [], [], self.timeout)
            if out:
                res = self.solver_stdout.readline().strip()
            else:
                self.exit()
                self.recreate_process()
                raise TimeoutExpired(cmd=self.NAME, timeout=self.timeout)
        self._debug("Read: %s", res)
        return res

    def run(self, path: Path, timeout: Optional[int] = None) -> Status:
        """
        Run the solver on the provided SMT-LIBv2 file.
        If the output is sat/unsat + something, the status will
        parsed and stored internally.
        If unsat, the following output is stored as the proof.
        Otherwise, PyCHCUnknownResultException is raised.
        """
        if path is None or not path.is_file():
            raise PyCHCSolverException("Provided path is not a valid file")

        from pychc.parser import scan_commands_in_smtlib_file

        self.set_timeout(timeout)

        commands = scan_commands_in_smtlib_file(path)
        for cmd in commands:
            if cmd == "(exit)":
                continue  # we will exit later
            self._send_raw_command(cmd)
            if cmd == "(push)":
                self.push()
            elif cmd == "(pop)":
                self.pop()
            elif cmd == "(get-model)":
                self.get_model()
            elif cmd == "(get-proof)":
                self.get_proof()
            else:
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

        return self._status
