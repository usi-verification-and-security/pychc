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

from pysmt.logics import QF_LRA, QF_LIA, QF_LIRA, QF_UFLIA, QF_UFLRA, UFLIRA

from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions


class OpenSMTOptions(SMTSolverOptions):
    """
    Options for OpenSMT solver.
    """


class OpenSMTSolver(SMTSolver):
    """OpenSMT SMT solver adapter using SMT-LIB textual interface."""

    NAME = "opensmt"
    LOGICS = (QF_LRA, QF_LIA, QF_LIRA, QF_UFLIA, QF_UFLRA, UFLIRA)
    OptionsClass = OpenSMTOptions
