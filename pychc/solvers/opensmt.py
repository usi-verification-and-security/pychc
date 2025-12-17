from __future__ import annotations

from pathlib import Path
from typing import Optional

from pysmt.logics import QF_LRA, QF_LIA, Logic

from pychc.exceptions import PyCHCSolverException
from pychc.solvers.witness import ProofFormat
from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions


class OpenSMTOptions(SMTSolverOptions):
    """
    Options for OpenSMT solver. Inherits SMTSolverOptions.
    No additional set-options are required beyond proofs configuration.
    """

    def __init__(self, proof_format: Optional[ProofFormat] = None, **base_options):
        super().__init__(**base_options)
        if proof_format:
            raise PyCHCSolverException(f"OpenSMT only supports native proof format.")


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
