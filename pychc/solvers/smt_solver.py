from __future__ import annotations

import tempfile, logging

from io import StringIO
from pathlib import Path
from select import select
from shutil import which

from time import time
from typing import Optional

from pysmt.smtlib.solver import SmtLibSolver, SmtLibOptions
from pysmt.environment import get_env
from pysmt.logics import Logic

from pychc.solvers.witness import ProofFormat
from pychc.solvers.proof_checker import ProofChecker
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException, PyCHCInternalException


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
        logic: Logic,
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

        if not any(logic <= l for l in self.LOGICS):
            raise PyCHCSolverException(
                f"Logic {logic} not supported by solver {self.NAME}"
            )
        # Try to upgrade to quantified logic, if supported
        q_logic = logic.get_quantified_version()
        if not any(logic <= l for l in self.LOGICS):
            self.logic = q_logic
        else:
            self.logic = logic

        # Needed to track relevant commands for proof checking
        self.commands = [[]]

        # Create an interactive subprocess with the solver binary
        env = get_env()
        args = [str(self._solver_path)] + (cmd_args if cmd_args else [])
        super().__init__(
            args=args, environment=env, logic=logic, LOGICS=self.LOGICS, **options
        )

        self.set_proof_checker(proof_checker)

    def get_logic(self) -> Logic:
        return self.logic

    def set_proof_checker(self, proof_checker: Optional[ProofChecker]) -> None:
        """
        Set or change the proof checker used for validating proofs.
        """
        self.proof_checker = proof_checker
        if proof_checker is None:
            self.options.set_produce_proofs(False)
        else:
            self.options.set_produce_proofs(True, proof_checker.get_proof_format())
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
        self.delete_files()
        self._debug("Sending: %s", cmd.serialize_to_string())
        string_io = StringIO()
        cmd.serialize(string_io, daggify=True)
        val = string_io.getvalue()
        self.commands[-1].append(val.strip())
        self.solver_stdin.write(val)
        self.solver_stdin.write("\n")
        self.solver_stdin.flush()

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
        return self._get_long_answer()

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
        self.get_proof_file()
        self.get_smt2_file()
        ok = self.proof_checker.validate(self.proof_file, self.smt2file)
        if not ok:
            raise PyCHCInvalidResultException(
                f"SMT solver {SMTSolver.NAME} produced an invalid proof. See proof file: {self.get_proof_file()} for query {self.get_smt2_file()}")
        self.delete_files()

    def _get_long_answer(self) -> str:
        # Read all currently available output:
        # Block until the first data chunk arrives (or max timeout elapses)
        # After first data, switch to idle-timeout mode to detect completion
        # Enforce a hard max timeout of 10s for the entire read
        buf: list[str] = []
        start = time()
        idle_timeout = 0.1  # seconds to wait for more data after first chunk
        max_timeout = 10.0  # hard cap for overall read

        fd = self.solver.stdout  # raw buffered reader from Popen
        got_first_chunk = False

        while True:
            remaining = max_timeout - (time() - start)
            if remaining <= 0:
                break

            # Before first chunk: wait up to remaining time (blocking)
            # After first chunk: wait only idle_timeout (bounded by remaining)
            wait = remaining if not got_first_chunk else min(idle_timeout, remaining)
            rlist, _, _ = select([fd], [], [], wait)
            if rlist:
                chunk = fd.read1(8192)
                if not chunk:
                    # EOF
                    break
                buf.append(chunk.decode("utf-8", errors="replace"))
                got_first_chunk = True
                continue
            else:
                # No data arrived within the wait window
                if got_first_chunk:
                    # Consider stream idle -> done
                    break
                # Otherwise, keep waiting until max_timeout expires
                continue

        proof = "".join(buf).strip()
        self._debug("Read proof bytes: %d", len(proof))
        return proof
