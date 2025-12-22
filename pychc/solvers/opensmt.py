from __future__ import annotations

from pathlib import Path
from typing import Optional

from pysmt.logics import QF_LRA, QF_LIA, Logic

from pychc.exceptions import PyCHCSolverException
from pychc.solvers.witness import ProofFormat
from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions


class OpenSMTOptions(SMTSolverOptions):
    """
    Options for OpenSMT solver.
    """


class OpenSMTSolver(SMTSolver):
    """OpenSMT SMT solver adapter using SMT-LIB textual interface."""

    NAME = "opensmt"
    LOGICS = (QF_LRA, QF_LIA)
    OptionsClass = OpenSMTOptions
