from __future__ import annotations

import tempfile, logging

from shutil import which
from pathlib import Path
from abc import ABC, abstractmethod
from subprocess import run, CalledProcessError, TimeoutExpired
from typing import Optional

from pychc.solvers.proof_checker import ProofChecker
from pychc.solvers.smt_solver import SMTSolver
from pychc.solvers.witness import SatWitness, UnsatWitness, Witness, Status, ProofFormat
from pychc.chc_system import CHCSystem
from pychc.exceptions import (
    PyCHCException,
    PyCHCInvalidResultException,
    PyCHCSolverException,
    PyCHCInternalException,
)


class CHCSolverOptions(ABC):
    """
    Abstract base class for solver options.
    """

    PROOF_FORMATS: set[ProofFormat] = set()

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

    def _remove_option(self, option: str):
        if option in self._options:
            del self._options[option]

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

    def __init__(
        self,
        binary_path: Optional[Path] = None,
        smt_validator: Optional[SMTSolver] = None,
        proof_checker: Optional[ProofChecker] = None,
    ):
        self.system: Optional[CHCSystem] = None

        self._status: Optional[Status] = None
        self._raw_output: Optional[str] = None
        self._witness: Optional[Witness] = None

        self.chc_options: CHCSolverOptions = self.OPTION_CLASS()

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

        self.set_smt_validator(smt_validator)
        self.set_proof_checker(proof_checker)

    def set_smt_validator(self, smt_validator: Optional[SMTSolver]) -> None:
        """
        Set the underlying SMT solver to use.
        """
        self.smt_validator = smt_validator

    def set_unsat_proof_format(self, proof_format: ProofFormat) -> None:
        """
        Set the proof format to use for UNSAT proofs.
        """
        if proof_format:
            self.chc_options.set_print_witness(True, proof_format)
        else:
            self.chc_options.set_print_witness(False)
        self.proof_format = proof_format
        if self.proof_checker and self.proof_checker.get_proof_format() != proof_format:
            self.proof_checker = None
            logging.warning("Changing proof format, unsetting existing proof checker.")

    def set_proof_checker(self, proof_checker: Optional[ProofChecker]) -> None:
        """
        Set the proof checker to use for validating UNSAT proofs.
        """
        proof_format = proof_checker.get_proof_format() if proof_checker else None
        if proof_format:
            self.chc_options.set_print_witness(True, proof_format)
        else:
            self.chc_options.set_print_witness(False)
        self.proof_checker = proof_checker
        self.proof_format = proof_format

    def load_system(self, chc_system: CHCSystem) -> None:
        """
        Load a CHC system into the solver.
        """
        if self.system:
            logging.warning("Overwriting existing CHC system in solver")
            self._witness = None
            self._status = None
            self._raw_output = None
        self.system = chc_system

    def get_input_file(self) -> Path:
        # This method is possibly overridden by subclasses
        # to add a (get-model) command.
        input_file = self.system.get_smt2file()
        return input_file

    def solve(self, timeout: Optional[int] = None, validate=False) -> Status:
        """
        Run the solver on the provided CHC system.

        :param timeout: optional timeout in seconds
        :return: solving status (SAT/UNSAT/UNKNOWN)
        """

        if not self.system:
            raise PyCHCSolverException("No CHC system loaded in solver")

        # Always ask for a witness.
        expected_validation = True  # self.smt_validator or self.proof_format
        self.chc_options.set_print_witness(expected_validation, self.proof_format)
        args_extra = self.chc_options.to_array()

        # serialize the input system
        input_file = self.get_input_file()

        args = [str(self._solver_path), str(input_file)] + args_extra
        try:
            logging.debug(f"Running {self.NAME}: {' '.join(args)}")
            proc = run(
                args, capture_output=True, text=True, check=True, timeout=timeout
            )
        except CalledProcessError as err:
            self._raw_output = (err.stdout or "") + (err.stderr or "")
            logging.error(f"{self.NAME} execution failed: {self._raw_output}")
            self._status = Status.UNKNOWN
            raise PyCHCSolverException(f"{self.NAME} execution failed")
        except TimeoutExpired as err:
            logging.error(f"{self.NAME} execution timed out after {timeout} seconds")
            self._status = Status.UNKNOWN
            return self._status

        raw_output = (proc.stdout or "").strip()

        # Understand if SAT/UNSAT/UNKNOWN
        # this sets self._status and self._raw_output
        self._decide_result(raw_output)

        if self._status != Status.UNKNOWN and validate:
            self.validate_witness()

        return self._status

    def get_witness(self) -> Optional[Witness]:
        """
        Return a model/witness. Must be called after a `solve()` with `get_witness=True`
        that returned `Status.SAT` or `Status.UNSAT`.
        """
        if self._witness:
            return self._witness

        if not self._raw_output or self._status == Status.UNKNOWN:
            self._witness = None
        elif self._status == Status.SAT:
            self._witness = SatWitness.load_from_text(self._raw_output)
            if not self.system.check_witness_consistency(self._witness):
                raise PyCHCInvalidResultException(
                    "Extracted model is not consistent with the CHC system predicates."
                )
        else:
            self._witness = UnsatWitness(self._raw_output, self.proof_format)

        return self._witness

    def validate_witness(self):
        if not self._witness:
            self.get_witness()
        assert self._witness
        if self._status == Status.SAT:
            if not self.smt_validator:
                raise PyCHCException(
                    "No SMT validator set for requested witness validation."
                )
            self.system.validate_sat_model(self._witness, self.smt_validator)
        elif self._status == Status.UNSAT:
            if not self.proof_checker:
                raise PyCHCException(
                    "No proof checker set for requested proof validation."
                )
            self.system.validate_unsat_proof(self._witness, self.proof_checker)
        else:
            raise PyCHCException("Cannot validate witness for UNKNOWN status.")

    def get_status(self) -> Optional[Status]:
        """
        Return the solving status. Must be called after `solve()`.
        """
        return self._status

    def _decide_result(self, text: str) -> None:
        """
        Decide the solving result (SAT/UNSAT/UNKNOWN) from the solver output.
        Sets self._status: Status and self._raw_output: str.
        """
        # status is first line, the rest is self._raw_output
        status, *rest = text.splitlines()
        if status == "sat":
            self._status = Status.SAT
            # also remove open-close brackets
            assert not rest or (rest[0].strip() == "(" and rest[-1].strip() == ")")
            self._raw_output = "\n".join(rest[1:-1]).strip() if rest else ""
        elif status == "unsat":
            self._status = Status.UNSAT
            self._raw_output = "\n".join(rest).strip()
        else:
            self._status = Status.UNKNOWN
