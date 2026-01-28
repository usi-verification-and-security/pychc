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

from pathlib import Path
from typing import Optional

from pysmt.logics import (
    Logic,
    QF_LRA,
    QF_LIA,
    QF_LIRA,
    QF_UFLIA,
    QF_UFLRA,
    LIA,
    LRA,
    UFLIRA,
)

from pychc.solvers.witness import ProofFormat
from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions


class CVC5Options(SMTSolverOptions):
    """
    Options for CVC5 SMT solver.
    """

    PROOF_FORMATS = {ProofFormat.ALETHE, ProofFormat.LFSC, ProofFormat.DOT}

    def __call__(self, solver):
        # Base options (including produce-proofs)
        super().__call__(solver)
        if self.proof_format:
            solver.set_option(":proof-format-mode", self.proof_format.value)


class CVC5Solver(SMTSolver):
    """CVC5 SMT solver adapter using SMT-LIB textual interface."""

    NAME = "cvc5"
    LOGICS = (QF_LRA, QF_LIA, QF_LIRA, QF_UFLIA, QF_UFLRA, LIA, LRA, UFLIRA)
    OptionsClass = CVC5Options

    def __init__(
        self,
        logic: Optional[Logic] = None,
        binary_path: Optional[Path] = None,
        **options,
    ):
        super().__init__(
            logic=logic, binary_path=binary_path, cmd_args=["--incremental"], **options
        )
