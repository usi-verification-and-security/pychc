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
from pathlib import Path
from abc import ABC, abstractmethod
from shutil import which
from subprocess import CalledProcessError, run, TimeoutExpired
import tempfile
from typing import Optional

from pychc.exceptions import (
    PyCHCSolverException,
    PyCHCInternalException,
    PyCHCInvalidResultException,
)
from pychc.solvers.witness import ProofFormat, UnsatWitness


class ProofCheckerOptions:
    """
    Options container for proof checkers.
    """

    def __init__(self, **_: object):
        self._options: dict[str, object] = {}
        self.mode = None
        self._flags: set[str] = set()

    def to_array(self) -> list[str]:
        res: list[str] = [self.mode] if self.mode else []
        for opt, val in self._options.items():
            res.append(str(opt))
            res.append(str(val))
        res.extend(sorted(self._flags))
        return res

    def set_mode(self, mode: str) -> None:
        self.mode = mode

    def set_flag(self, flag: str, enable: bool = True) -> None:
        if enable:
            self._flags.add(flag)
        else:
            self._flags.discard(flag)

    def set_option(self, option: str, value: object) -> None:
        self._options[option] = value


class ProofChecker(ABC):
    """
    Abstract base class for proof checkers.
    """

    NAME: str = ""
    OPTION_CLASS = ProofCheckerOptions

    def __init__(self, binary_dir: Optional[Path] = None, **options):
        if not self.NAME:
            raise PyCHCInternalException(
                "ProofChecker.NAME must be defined by subclass"
            )

        checker_path = which(self.NAME, path=str(binary_dir) if binary_dir else None)
        if not checker_path:
            raise PyCHCSolverException(f"{self.NAME} executable not found")

        self._checker_path = Path(checker_path)
        if not self._checker_path.is_file():
            raise PyCHCSolverException(
                f"{self.NAME} executable not found at: {self._checker_path}"
            )

        # Instantiate options container (subclasses may provide custom OPTION_CLASS)
        self.options: ProofCheckerOptions = self.OPTION_CLASS(**options)

        self._raw_output: Optional[str] = None

    @abstractmethod
    def get_proof_format(self) -> Optional[ProofFormat]:
        """
        Get the proof format used by this proof checker, if any.
        """

    def validate_witness(
        self, witness: UnsatWitness, smt2file: Path, timeout: Optional[int] = None
    ) -> bool:
        """
        Validate the proof contained in the witness against the given smt2 file.
        """
        proof_file = Path(tempfile.NamedTemporaryFile("w", suffix=".proof").name)
        with open(proof_file, "w") as pf:
            pf.write(witness.text)

        ok = self.validate(proof_file=proof_file, smt2file=smt2file, timeout=timeout)
        if not ok:
            raise PyCHCInvalidResultException(
                f"Proof checker {self.NAME} failed to validate the proof {proof_file} on {smt2file}."
            )
        # if everything went fine, delete temp file
        proof_file.unlink()

    def validate(
        self, proof_file: Path, smt2file: Path, timeout: Optional[int] = None
    ) -> bool:
        args = (
            [str(self._checker_path)]
            + self.options.to_array()
            + [str(proof_file), str(smt2file)]
        )
        try:
            logging.debug(f"Running {self.NAME}: {' '.join(args)}")
            proc = run(
                args, capture_output=True, text=True, check=True, timeout=timeout
            )
        except CalledProcessError as err:
            self._raw_output = (err.stdout or "") + (err.stderr or "")
            logging.error(f"{self.NAME} execution failed: {self._raw_output}")
            logging.error(f"Command: {' '.join(args)}")
            return False
        except TimeoutExpired:
            logging.error(f"{self.NAME} execution timed out after {timeout} seconds")
            raise PyCHCSolverException(f"{self.NAME} execution timed out")

        self._raw_output = (proc.stdout or "").strip()
        return self._decide_result()

    @abstractmethod
    def _decide_result(self) -> bool:
        """
        Decide boolean result based on `self._raw_output`.
        """
