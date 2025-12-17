from __future__ import annotations

import tempfile, logging

from shutil import which
from pathlib import Path
from abc import ABC, abstractmethod
from subprocess import run, CalledProcessError, TimeoutExpired

from typing import Optional

from pychc.solvers.witness import SatWitness, UnsatWitness, Witness, Status, ProofFormat
from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCSolverException, PyCHCInternalException


class CHCSolverOptions(ABC):
    """
    Abstract base class for solver options.
    """

    PROOF_FORMATS: set[ProofFormat] = set()

    def __init__(
        self, print_witness: bool = False, proof_format: Optional[ProofFormat] = None
    ):
        self._options = {}
        self._flags = set()
        self.set_print_witness(print_witness, proof_format)

    def to_array(self) -> list[str]:
        """Convert options to CLI args list."""

        res = []
        for opt, val in self._options.items():
            res.append(str(opt))
            res.append(str(val))
        res.extend(self._flags)
        return res

    def _set_flag(self, flag: str, value: bool = True):
        if value:
            self._flags.add(flag)
        else:
            self._flags.discard(flag)

    def _set_option(self, option: str, value):
        self._options[option] = value

    @abstractmethod
    def set_print_witness(
        self, enable: bool, proof_format: Optional[ProofFormat] = None
    ) -> None:
        """
        Enable or disable printing of witness/model in the solver output.
        """


class CHCSolver(ABC):
    """
    Abstract base class for CHC solvers.
    """

    NAME: str = ""
    OPTION_CLASS = CHCSolverOptions

    def __init__(self, binary_path: Optional[Path] = None, **options):
        """
        Initialize the solver with a CHC system.

        :param chc_system: CHC system to solve
        """

        self.system: Optional[CHCSystem] = None
        self._status: Optional[Status] = None
        self._witness: Optional[Witness] = None

        self.options: CHCSolverOptions = self.OPTION_CLASS(**options)

        if not self.NAME:
            raise PyCHCInternalException("CHCSolver.NAME must be defined by subclass")
        solver_path = which(self.NAME, path=str(binary_path) if binary_path else None)
        if not solver_path:
            raise PyCHCSolverException(f"{self.NAME} executable not found")
        self._solver_path = Path(solver_path)
        if not self._solver_path.is_file():
            raise PyCHCSolverException(
                f"{self.NAME} executable not found at: {self._solver_path}"
            )

    def load_system(self, chc_system: CHCSystem) -> None:
        """
        Load a CHC system into the solver.
        """
        if self.system:
            logging.warning("Overwriting existing CHC system in solver")
            self._witness = None
            self._status = None
        self.system = chc_system

    def solve(
        self,
        get_witness: bool = False,
        proof_format: Optional[ProofFormat] = None,
        timeout: Optional[int] = None,
    ) -> Status:
        """
        Run the solver on the provided CHC system.

        :param get_witness: whether to create a witness/model while solving
        """

        if not self.system:
            raise PyCHCSolverException("No CHC system loaded in solver")

        self.options.set_print_witness(get_witness, proof_format)

        args_extra = self.options.to_array()

        with tempfile.NamedTemporaryFile("w", suffix=".smt2") as input_path:
            self.system.serialize(Path(input_path.name))
            args = [str(self._solver_path), str(input_path.name)] + args_extra
            try:
                logging.debug(f"Running {self.NAME}: {' '.join(args)}")
                proc = run(
                    args, capture_output=True, text=True, check=True, timeout=timeout
                )
            except CalledProcessError as err:
                raw_output = (err.stdout or "") + (err.stderr or "")
                logging.error(f"{self.NAME} execution failed: {raw_output}")
                self._status = Status.UNKNOWN
                raise PyCHCSolverException(f"{self.NAME} execution failed")
            except TimeoutExpired as err:
                logging.error(
                    f"{self.NAME} execution timed out after {timeout} seconds"
                )
                self._status = Status.UNKNOWN
                return self._status

            raw_output = (proc.stdout or "").strip()

            # Understand if SAT/UNSAT/UNKNOWN
            self._status = self.decide_result(raw_output)

            if not get_witness or self._status == Status.UNKNOWN:
                self._witness = None
                return self._status

            # Extract witness
            if self._status == Status.SAT:
                self._witness = self.extract_model(raw_output)
            else:
                self._witness = self.extract_unsat_proof(raw_output, proof_format)

            return self._status

    def get_witness(self) -> Optional[Witness]:
        """
        Return a model/witness. Must be called after a `solve()` with `get_witness=True`
        that returned `Status.SAT` or `Status.UNSAT`.
        """
        return self._witness

    @abstractmethod
    def decide_result(self, output: str) -> Status:
        """
        Decide the solving result (SAT/UNSAT/UNKNOWN) from the solver output.
        """

    @abstractmethod
    def extract_model(self, output: str) -> SatWitness:
        """
        Extract a SAT witness/model from the solver output.
        """

    @abstractmethod
    def extract_unsat_proof(
        self, output: str, proof_format: Optional[ProofFormat]
    ) -> UnsatWitness:
        """
        Extract an UNSAT proof from the solver output.
        """
