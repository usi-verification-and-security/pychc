from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Optional

from pychc.solvers.chc_witness import CHCWitness, CHCStatus
from pychc.chc_system import CHCSystem

class CHCSolver(ABC):
    """
    Abstract base class for CHC solvers.
    """

    def __init__(self, chc_system: CHCSystem):
        """
        Initialize the solver with a CHC system.

        :param chc_system: CHC system to solve
        """

        self.system = chc_system
        self._status: Optional[CHCStatus] = None
        self._witness: Optional[CHCWitness] = None

    @abstractmethod
    def solve(self, get_witness: bool = False) -> CHCStatus:
        """
        Run the solver on the provided CHC system.

        :param get_witness: whether to create a witness/model while solving
        """

    @abstractmethod
    def get_witness(self) -> CHCWitness:
        """
        Return a model/witness. Must be called after a `solve()` with `get_witness=True`
        that returned `CHCStatus.SAT` or `CHCStatus.UNSAT`.
        """


# eoc CHCSolver
