"""
Golem instance of CHCSolver
"""

from __future__ import annotations

from typing import Optional

from pychc.solvers.witness import ProofFormat, UnsatWitness
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.exceptions import PyCHCSolverException


class GolemOptions(CHCSolverOptions):
    """Options passed to the Golem process via command line flags."""

    PROOF_FORMATS = {ProofFormat.LEGACY, ProofFormat.INTERMEDIATE, ProofFormat.ALETHE}

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        """Enable `--print-witness` to request witness output."""
        self._set_flag("--print-witness", value)
        if not value or proof_format is None:
            self._remove_option("--proof-format")
        else:
            if proof_format not in self.PROOF_FORMATS:
                raise PyCHCSolverException(
                    f"Unsupported proof format for Golem: {proof_format}"
                )
            self._set_option(f"--proof-format", proof_format.value)


class GolemSolver(CHCSolver):
    """Solver adapter for the Golem CHC solver."""

    NAME = "golem"
    OPTION_CLASS = GolemOptions
