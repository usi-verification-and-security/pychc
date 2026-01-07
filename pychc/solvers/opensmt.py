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
