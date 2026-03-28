#
# Copyright 2026 Martin Blicha
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

from typing import Optional

from pychc.solvers.witness import ProofFormat
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.exceptions import PyCHCSolverException


class EldaricaOptions(CHCSolverOptions):
    """Options passed to the Eldarica process via command line flags."""

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        if value and proof_format:
            raise PyCHCSolverException(
                "Eldarica does not support custom proof formats."
            )
        self._set_flag("-scex", value)
        self._set_flag("-ssol", value)


class EldaricaSolver(CHCSolver):
    """Solver adapter for the Eldarica CHC solver."""

    NAME = "eld"
    OPTION_CLASS = EldaricaOptions
