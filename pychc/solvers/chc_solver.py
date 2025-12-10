from __future__ import annotations

import tempfile, logging

from shutil import which
from pathlib import Path
from abc import ABC, abstractmethod
from subprocess import run, CalledProcessError

from typing import Optional

from pychc.solvers.chc_witness import CHCWitness, CHCStatus
from pychc.chc_system import CHCSystem
from pychc.exceptions import PyCHCSolverException


class Options(ABC):
    """
    Abstract base class for solver options.
    """

    def __init__(self):
        self._options = {}
        self._flags = set()

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

    @abstractmethod
    def enable_print_witness(self, enable: bool) -> None:
        """
        Enable or disable printing of witness/model in the solver output.
        """


class CHCSolver(ABC):
    """
    Abstract base class for CHC solvers.
    """

    NAME = "abstract_solver"
    OPTION_CLASS = Options

    def __init__(self, chc_system: CHCSystem, binary_path: Optional[Path] = None):
        """
        Initialize the solver with a CHC system.

        :param chc_system: CHC system to solve
        """

        self.system: CHCSystem = chc_system
        self._status: Optional[CHCStatus] = None
        self._witness: Optional[CHCWitness] = None

        self.options: Options = self.OPTION_CLASS()

        if binary_path:
            solver_path = which(self.NAME, path=str(binary_path))
        else:
            solver_path = which(self.NAME)
        if not solver_path:
            raise PyCHCSolverException(f"{self.NAME} executable not found")
        self._solver_path = Path(solver_path)
        if not self._solver_path.is_file():
            raise PyCHCSolverException(
                f"{self.NAME} executable not found at: {self._solver_path}"
            )

    def solve(self, get_witness: bool = False) -> CHCStatus:
        """
        Run the solver on the provided CHC system.

        :param get_witness: whether to create a witness/model while solving
        """
        if get_witness:
            self.options.enable_print_witness(True)

        args_extra = self.options.to_array()

        with tempfile.NamedTemporaryFile("w", suffix=".smt2") as input_path:
            self.system.serialize(Path(input_path.name))
            args = [str(self._solver_path), str(input_path.name)] + args_extra
            try:
                logging.debug(f"Running {self.NAME}: {' '.join(args)}")
                proc = run(args, capture_output=True, text=True, check=True)
            except CalledProcessError as err:
                raw_output = (err.stdout or "") + (err.stderr or "")
                logging.error(f"{self.NAME} execution failed: {raw_output}")
                self._status = CHCStatus.UNKNOWN
                raise PyCHCSolverException(f"{self.NAME} execution failed")

            raw_output = (proc.stdout or "").strip()

            # Understand if SAT/UNSAT/UNKNOWN
            self._status = self.decide_result(raw_output)

            if not get_witness or self._status == CHCStatus.UNKNOWN:
                return self._status

            # Extract witness
            if self._status == CHCStatus.SAT:
                self._witness = self.extract_model(raw_output)
            else:
                self._witness = self.extract_unsat_proof(raw_output)

            return self._status

    def get_witness(self) -> Optional[CHCWitness]:
        """
        Return a model/witness. Must be called after a `solve()` with `get_witness=True`
        that returned `CHCStatus.SAT` or `CHCStatus.UNSAT`.
        """
        return self._witness

    @abstractmethod
    def decide_result(self, output: str) -> CHCStatus:
        """
        Decide the solving result (SAT/UNSAT/UNKNOWN) from the solver output.
        """

    @abstractmethod
    def extract_model(self, output: str) -> Optional[CHCWitness]:
        """
        Extract a SAT witness/model from the solver output.
        """

    @abstractmethod
    def extract_unsat_proof(self, output: str) -> Optional[CHCWitness]:
        """
        Extract an UNSAT proof from the solver output.
        """
