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

from enum import Enum
from typing import Optional

from pychc.solvers.witness import ProofFormat, UnsatWitness
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.exceptions import PyCHCSolverException


class GolemEngines(str, Enum):
    """Available engines for Golem."""
    bmc = "bmc"             # Bounded Model Checking (only linear systems)
    dar = "dar"             # Dual Approximated Reachability (only linear systems)   
    imc = "imc"             # McMillan's original Interpolation-based model checking (only linear systems)
    kind = "kind"           # basic k-induction algorithm (only transition systems)
    lawi = "lawi"           # Lazy Abstraction with Interpolants (only linear systems)
    pa = "pa"               # basic predicate abstraction with CEGAR (any system)
    pdkind = "pdkind"       # Property directed k-induction (only linear systems)
    se = "se"               # forward symbolic execution (only linear system)
    spacer = "spacer"       # custom implementation of Spacer (any system)
    split_tpa = "split-tpa" # Split Transition Power Abstraction (only linear systems)
    tpa = "tpa"             # Transition Power Abstraction (only linear systems)
    trl = "trl"             # Transitive Relations Learning (only linear systems)


class GolemOptions(CHCSolverOptions):
    """Options passed to the Golem process via command line flags."""

    PROOF_FORMATS = {ProofFormat.LEGACY, ProofFormat.INTERMEDIATE, ProofFormat.ALETHE}

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        """Enable `--print-witness` to request witness output."""
        self._set_flag("--print-witness", value)
        if not value or proof_format is None:
            self._remove_option("--proof-format")
        else:
            if proof_format not in self.PROOF_FORMATS:
                raise PyCHCSolverException(
                    f"Unsupported proof format for Golem: {proof_format}"
                )
            self._set_option(f"--proof-format", proof_format.value)
        
    def use_engine(self, engine: GolemEngines) -> None:
        """Set the engine to be used by Golem."""
        self._set_option("--engine", engine.value)


class GolemSolver(CHCSolver):
    """Solver adapter for the Golem CHC solver."""

    NAME = "golem"
    OPTION_CLASS = GolemOptions

    def __init__(self, engine: Optional[GolemEngines] = None, **args):
        CHCSolver.__init__(self, **args)
        if engine:
            self.chc_options.use_engine(engine)

