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
        logic: Logic,
        binary_path: Optional[Path] = None,
        **options,
    ):
        super().__init__(
            logic=logic, binary_path=binary_path, cmd_args=["--incremental"], **options
        )
