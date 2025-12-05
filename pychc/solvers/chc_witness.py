from abc import ABC
from enum import Enum

from pysmt.substituter import FunctionInterpretation

class CHCWitness(ABC):
    """Abstract witness produced by a CHC solver."""
    pass


class SatWitness(CHCWitness):
    ''' A Sat witness is an interpretation for the predicates '''
    def __init__(self, definitions: dict[str, FunctionInterpretation]):
        self.definitions = definitions


class UnsatWitness(CHCWitness):
    """Abstract UNSAT witness (proof/certificate) produced by a CHC solver."""
    pass


class CHCStatus(str, Enum):
    """Outcome of solving a CHC system."""
    
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"


