from __future__ import annotations

from abc import abstractmethod
from pathlib import Path
from select import select
from shutil import which
from time import time
from typing import Optional

from pysmt.smtlib.solver import SmtLibSolver, SmtLibOptions
from pysmt.smtlib.script import SmtLibCommand
from pysmt.smtlib import commands as smtcmd
from pysmt.environment import get_env
from pysmt.logics import Logic

from pychc.exceptions import PyCHCSolverException, PyCHCInternalException


class SMTSolverOptions(SmtLibOptions):
    """
    Options for SMTSolver extending pySMT's SmtLibOptions with proof support.

    Adds:
    - produce_proofs: when True sets `:produce-proofs` to `true`.
    - Additional `solver_options` passed through as standard SMT-LIB `set-option`.
    """

    def __init__(self, produce_proofs: bool = True, **base_options):
        super().__init__(**base_options)
        self.produce_proofs = produce_proofs

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

    NAME: str = ""  # to be set by concrete subclasses
    LOGICS = None  # optional logic set override
    OptionsClass = SMTSolverOptions

    def __init__(
        self,
        logic: Logic,
        binary_path: Optional[Path] = None,
        cmd_args: Optional[list[str]] = None,
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
        # Create an interactive subprocess with the solver binary
        env = get_env()
        args = [str(self._solver_path)] + (cmd_args if cmd_args else [])
        super().__init__(
            args=args, environment=env, logic=logic, LOGICS=self.LOGICS, **options
        )

    def _send_command_get_proof(self):
        # NOTE: Workaround to the lack of GET_PROOF serialization in pySMT
        # The following is mocking:
        #     self._send_command(SmtLibCommand(smtcmd.GET_PROOF, []))
        self._debug(f"Sending: (get-proof)")
        self.solver_stdin.write(f"(get-proof)\n")
        self.solver_stdin.flush()

    def get_proof(self) -> str:
        """
        Request a proof/certificate from the solver using `(get-proof)`.

        Returns the raw proof text from the solver stdout.
        """
        self._send_command_get_proof()

        proof = self._read_proof_output()
        return proof

    def _read_proof_output(self) -> str:
        # Read all currently available output
        # Uses `select.select` to poll for readability and accumulates chunks until
        # the stream is idle for a short timeout. This handles empty lines and
        # large multi-line outputs without blocking indefinitely.
        buf: list[str] = []
        start = time()
        idle_timeout = 0.05  # seconds to wait for more data
        max_total = 10.0  # safety cap to avoid infinite loops

        fd = self.solver.stdout  # raw buffered reader from Popen
        while True:
            rlist, _, _ = select([fd], [], [], idle_timeout)
            if rlist:
                # Read a reasonable chunk to drain buffer
                chunk = fd.read1(8192)
                if not chunk:
                    break
                buf.append(chunk.decode("utf-8", errors="replace"))
            else:
                # No data ready -> assume solver is waiting for next input
                break
            if time() - start > max_total:
                break

        proof = "".join(buf).strip()
        self._debug("Read proof bytes: %d", len(proof))
        return proof
