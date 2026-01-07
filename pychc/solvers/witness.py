from __future__ import annotations

import logging

from abc import ABC
from enum import Enum
from pathlib import Path

from pychc.exceptions import PyCHCInvalidResultException
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
    """
    SAT witness is an interpretation for the predicates.
    Stored as an interpreted formulae in pySMT FunctionInterpretation format.
    """

    @classmethod
    def load_from_text(cls, smt_text: str) -> SatWitness:
        from io import StringIO
        from pysmt.typing import BOOL
        from pychc.parser import CHCSmtLibParser

        predicates: dict[str, FunctionInterpretation] = {}

        parser = CHCSmtLibParser()
        script = parser.get_script(StringIO(smt_text))
        decls = script.filter_by_command_name(("define-fun"))
        for decl in decls:
            args = getattr(decl, "args", [])
            if len(args) == 4:
                if args[2] != BOOL:
                    raise PyCHCInvalidResultException("Cannot parse: \n" + smt_text)
                name = args[0]
                params = args[1]
                body = args[3]
                if not params:
                    interpretation = body
                else:
                    interpretation = FunctionInterpretation(
                        formal_params=params, function_body=body, allow_free_vars=False
                    )
                predicates[name] = interpretation
            else:
                logging.warning(f"Skipping malformed declaration? {decl}")

        return SatWitness(predicates)

    def __init__(self, definitions: dict[str, FunctionInterpretation]):
        self.definitions = definitions


class UnsatWitness(Witness):
    """
    UNSAT witness (proof/certificate) produced by a solver.
    Stored as plain text along with its format.
    """

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
