from abc import ABC
from enum import Enum
from pathlib import Path

from pysmt.substituter import FunctionInterpretation


class ProofFormat(str, Enum):
    ALETHE = "alethe"
    LFSC = "lfsc"
    DOT = "dot"
    LEGACY = "legacy"
    INTERMEDIATE = "intermediate"


class Witness(ABC):
    """Abstract witness produced by a solver."""

    pass


class SatWitness(Witness):
    """A Sat witness is an interpretation for the predicates"""

    def __init__(self, definitions: dict[str, FunctionInterpretation]):
        self.definitions = definitions


class UnsatWitness(Witness):
    """Abstract UNSAT witness (proof/certificate) produced by a solver."""

    def __init__(self, text: str, proof_format: ProofFormat):
        self.text = text
        self.proof_format = proof_format

    def serialize(self, path: Path) -> None:
        """Serialize the UNSAT witness to a file."""
        with open(path, "w") as f:
            f.write(self.text)


class Status(str, Enum):
    """Outcome of solving a CHC system."""

    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"
