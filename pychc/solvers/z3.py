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
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.solvers.smt_solver import SMTSolver, SMTSolverOptions
from pychc.exceptions import PyCHCSolverException


class Z3CHCOptions(CHCSolverOptions):
    """Options passed to the Z3 process via command line flags."""

    def __init__(self, **base_options):
        super().__init__(**base_options)
        self._set_flag("fp.spacer.global=true", True)

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        """Enable certificate printing"""
        if proof_format:
            raise PyCHCSolverException("Z3 does not support custom proof formats.")
        # self._set_flag("fp.print_certificate=true", value)


class Z3CHCSolver(CHCSolver):
    """Solver adapter for the Z3 CHC solver."""

    NAME = "z3"
    OPTION_CLASS = Z3CHCOptions

    def get_input_file(self) -> Path:
        # Create a temporary copy of the SMT2 file and append (get-model)
        import tempfile, shutil

        original: Path = self.system.get_smt2file()
        with tempfile.NamedTemporaryFile(
            mode="w", delete=False, suffix=original.suffix
        ) as tmp:
            tmp_path = Path(tmp.name)
            with open(original, "r") as src:
                shutil.copyfileobj(src, tmp)
            # Ensure final newline before appending command
            tmp.write("\n(get-model)\n")

        return tmp_path


class Z3SMTOptions(SMTSolverOptions):
    """
    Options for Z3 SMT solver.
    """

    PROOF_FORMATS = set()


class Z3SMTSolver(SMTSolver):
    """Z3 SMT solver adapter using SMT-LIB textual interface."""

    NAME = "z3"
    LOGICS = (QF_LRA, QF_LIA, QF_LIRA, QF_UFLIA, QF_UFLRA, LIA, LRA, UFLIRA)
    OptionsClass = Z3SMTOptions

    def __init__(
        self,
        logic: Logic,
        binary_path: Optional[Path] = None,
        **options,
    ):
        super().__init__(
            logic=logic, binary_path=binary_path, cmd_args=["-in"], **options
        )
