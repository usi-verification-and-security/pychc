from __future__ import annotations

from pathlib import Path
from typing import Optional

from pysmt.logics import QF_LRA, LRA, QF_LIA, LIA, Logic

from pychc.solvers.witness import ProofFormat
from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions


class CVC5Options(SMTSolverOptions):
    """
    Options for CVC5 SMT solver.

    Extends SMTSolverOptions with `proof_format` to select the proof output format.
    """

    PROOF_FORMATS = {ProofFormat.ALETHE, ProofFormat.LFSC, ProofFormat.DOT}

    def __init__(
        self, proof_format: Optional[ProofFormat] = ProofFormat.ALETHE, **base_options
    ):
        super().__init__(**base_options)
        if proof_format and proof_format not in self.PROOF_FORMATS:
            raise ValueError(f"Unsupported proof format for CVC5: {proof_format}")
        self.proof_format: Optional[ProofFormat] = proof_format

    def __call__(self, solver):
        # Base options (including produce-proofs)
        super().__call__(solver)
        if self.proof_format:
            solver.set_option(":proof-format-mode", self.proof_format.value)


class CVC5Solver(SMTSolver):
    """CVC5 SMT solver adapter using SMT-LIB textual interface."""

    NAME = "cvc5"
    LOGICS = (QF_LRA, QF_LIA)
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
