"""
Eldarica instance of CHCSolver
"""

from __future__ import annotations

from typing import Optional

from pychc.solvers.witness import ProofFormat
from pychc.solvers.chc_solver import CHCSolver, CHCSolverOptions
from pychc.exceptions import PyCHCSolverException


class EldaricaOptions(CHCSolverOptions):
    """Options passed to the Eldarica process via command line flags."""

    def set_print_witness(
        self, value: bool = True, proof_format: Optional[ProofFormat] = None
    ):
        if proof_format:
            raise PyCHCSolverException(
                "Eldarica does not support custom proof formats."
            )
        self._set_flag("-scex", value)
        self._set_flag("-ssol", value)


class EldaricaSolver(CHCSolver):
    """Solver adapter for the Eldarica CHC solver."""

    NAME = "eld"
    OPTION_CLASS = EldaricaOptions
