#
# Copyright 2026 Anna Becchi
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from __future__ import annotations

import logging

from shutil import which
from pathlib import Path
from abc import ABC, abstractmethod
from subprocess import run, CalledProcessError, TimeoutExpired
from typing import Optional

from pychc.parser import decide_result
from pychc.solvers.proof_checker import ProofChecker
from pychc.solvers.smt_solver import SMTSolver
from pychc.solvers.witness import SatWitness, UnsatWitness, Witness, Status, ProofFormat
from pychc.chc_system import CHCSystem
from pychc.exceptions import (
    PyCHCException,
    PyCHCInvalidResultException,
    PyCHCSolverException,
    PyCHCInternalException,
    PyCHCUnknownResultException,
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
        proof_format: Optional[ProofFormat] = None,
        name: Optional[str] = None,
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
        if proof_format:
            # If both proof checker and proof format are provided, 
            # proof_format overrides the proof checker's format.
            self.set_unsat_proof_format(proof_format)
        self._name = name if name else self.NAME

    def get_name(self) -> str:
        return self._name

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
        Stores solving status and witness internally.
        If validate=True, the witness is validated using the configured
        SMT validator or proof checker.
        Otherwise, the witness is not parsed and can be obtained later.
        """
        if not self.system:
            raise PyCHCSolverException("No CHC system loaded in solver")
        # serialize the input system
        input_file = self.get_input_file()
        self._run_and_read_output(input_file, timeout, validate)
        return self._status

    def run(self, path: Path, timeout: Optional[int] = None, validate=False) -> Status:
        """
        Run the solver on the provided CHC system file.
        If the output is sat + model or unsat + proof, it will be
        parsed and stored internally.
        Otherwise, PyCHCUnknownResultException is raised.
        """
        if path is None or not path.is_file():
            raise PyCHCSolverException("Provided path is not a valid file")
        self._run_and_read_output(path, timeout, validate)
        return self._status

    def _run_and_read_output(
        self, sys_file: Path, timeout: Optional[int] = None, validate=False
    ):
        # Always ask for a witness.
        expected_validation = True  # self.smt_validator or self.proof_format
        self.chc_options.set_print_witness(expected_validation, self.proof_format)
        args_extra = self.chc_options.to_array()

        args = [str(self._solver_path), str(sys_file)] + args_extra
        logging.debug(f"Running {self.NAME}: {' '.join(args)}")
        try:
            proc = run(
                args, capture_output=True, text=True, check=True, timeout=timeout
            )
        except CalledProcessError as err:
            self._raw_output = (err.stdout or "") + (err.stderr or "")
            logging.error(f"{self.NAME} execution failed: {self._raw_output}")
            self._status = Status.UNKNOWN
            raise PyCHCSolverException(f"{self.NAME} execution failed")
        except TimeoutExpired as err:
            logging.info(f"{self.NAME} execution timed out after {timeout} seconds")
            self._status = Status.UNKNOWN
            return self._status

        raw_output = (proc.stdout or "").strip()

        # Understand if SAT/UNSAT/UNKNOWN
        # this sets self._status and self._raw_output
        self._witness = None
        self._status, self._raw_output = decide_result(raw_output)

        if self._status != Status.UNKNOWN and validate:
            # parse and validate the witness
            self.validate_witness()

    def get_witness(self) -> Optional[Witness]:
        """
        Parses the output to obtain a witness.
        Must be called after a `solve()`.
        """
        if self._witness:
            return self._witness

        if not self._raw_output or self._status == Status.UNKNOWN:
            self._witness = None
        elif self._status == Status.SAT:
            try:
                self._witness = SatWitness.load_from_text(self._raw_output)
            except Exception as e:
                raise PyCHCSolverException(
                    f"Failed to parse SAT witness from solver output. {e}"
                )
            if self.system and not self.system.check_witness_consistency(self._witness):
                raise PyCHCInvalidResultException(
                    "Extracted model is not consistent with the CHC system predicates."
                )
        else:
            self._witness = UnsatWitness(self._raw_output, self.proof_format)

        return self._witness

    def validate_witness(self, timeout: Optional[int] = None) -> None:
        """
        Obtains and validates the witness.
        Raises PyCHCInvalidResultException if the witness is invalid.
        """
        if not self.system:
            raise PyCHCSolverException("No CHC system loaded in solver")
        if not self._witness:
            self.get_witness()
        assert self._witness
        if self._status == Status.SAT:
            if not self.smt_validator:
                raise PyCHCException(
                    "No SMT validator set for requested witness validation."
                )
            self.system.validate_sat_model(
                self._witness, self.smt_validator, timeout=timeout
            )
        elif self._status == Status.UNSAT:
            if not self.proof_checker:
                raise PyCHCException(
                    "No proof checker set for requested proof validation."
                )
            self.system.validate_unsat_proof(
                self._witness, self.proof_checker, timeout=timeout
            )
        else:
            raise PyCHCException("Cannot validate witness for UNKNOWN status.")

    def get_status(self) -> Optional[Status]:
        """
        Return the solving status. Must be called after `solve()`.
        """
        return self._status
