from __future__ import annotations

from pathlib import Path
from typing import Optional
from enum import Enum

from pysmt.logics import QF_LRA, LRA, QF_LIA, LIA, Logic

from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions


class ProofFormat(str, Enum):
    ALETHE = "alethe"
    LFSC = "lfsc"
    DOT = "dot"


class CVC5Options(SMTSolverOptions):
    """
    Options for CVC5 SMT solver.

    Extends SMTSolverOptions with `proof_format` to select the proof output format.
    """

    def __init__(
        self, proof_format: Optional[ProofFormat] = ProofFormat.ALETHE, **base_options
    ):
        super().__init__(**base_options)
        self.proof_format: Optional[ProofFormat] = proof_format

    def __call__(self, solver):
        # Base options (including produce-proofs)
        super().__call__(solver)
        if self.proof_format is not None:
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
