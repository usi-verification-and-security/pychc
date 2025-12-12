from __future__ import annotations

from pathlib import Path
from typing import Optional

from pysmt.logics import QF_LRA, QF_LIA, Logic
from pysmt.smtlib.script import SmtLibCommand
from pysmt.smtlib import commands as smtcmd

from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions


class OpenSMTOptions(SMTSolverOptions):
    """
    Options for OpenSMT solver. Inherits SMTSolverOptions.
    No additional set-options are required beyond proofs configuration.
    """

    pass


class OpenSMTSolver(SMTSolver):
    """OpenSMT SMT solver adapter using SMT-LIB textual interface."""

    NAME = "opensmt"
    LOGICS = (QF_LRA, QF_LIA)
    OptionsClass = OpenSMTOptions

    def __init__(
        self,
        logic: Logic,
        binary_path: Optional[Path] = None,
        **options,
    ):
        # OpenSMT supports incremental SMT-LIB; no extra options needed
        super().__init__(logic=logic, binary_path=binary_path, **options)
