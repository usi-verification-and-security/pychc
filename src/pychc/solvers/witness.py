#
# Copyright 2026 Anna Becchi
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from __future__ import annotations

import logging

from abc import ABC, abstractmethod
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

    @abstractmethod
    def serialize(self, path: Path) -> None:
        """Serialize the witness to a file."""
        pass
    
    @abstractmethod
    def serialize_to_string(self) -> str:
        """Serialize the witness to a string."""
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

    @classmethod
    def load_from_file(cls, path: Path) -> SatWitness:
        with open(path, "r") as f:
            smt_text = f.read()
        return cls.load_from_text(smt_text)

    def __init__(self, definitions: dict[str, FunctionInterpretation]):
        self.definitions = definitions

    def serialize(self, path: Path) -> None:
        """Serialize the SAT witness to a file."""
        with open(path, "w") as fout:
            self._serialize_to_stream(fout)
        
    def serialize_to_string(self) -> str:
        from io import StringIO

        with StringIO() as fout:
            self._serialize_to_stream(fout)
            return fout.getvalue()
    
    def _serialize_to_stream(self, fout) -> None:
        """Serialize the SAT witness to a file."""
        from pysmt.utils import quote
        from pysmt.typing import BOOL
        from pysmt.smtlib.printers import SmtPrinter

        booltype = BOOL.as_smtlib(funstyle=False)

        printer = SmtPrinter(fout)
        for name, interpretation in self.definitions.items():
            # Similar to SmtCommand.serialize, but taking care of quoting parameter's names
            name = quote(name)

            if not isinstance(interpretation, FunctionInterpretation):
                fout.write(f"\n(define-fun {name} () {booltype} ")
                printer.printer(interpretation)
                fout.write(")")
                continue

            params = " ".join(
                f"({quote(v.symbol_name())} {v.symbol_type().as_smtlib(funstyle=False)})"
                for v in interpretation.formal_params
            )
            fout.write(f"\n(define-fun {name} ({params}) {booltype} ")
            printer.printer(interpretation.function_body)
            fout.write(")")


class UnsatWitness(Witness):
    """
    UNSAT witness (proof/certificate) produced by a solver.
    Stored as plain text along with its format.
    """

    def __init__(self, text: str, proof_format: ProofFormat):
        self.text = text
        self.proof_format = proof_format

    @classmethod
    def load_from_file(cls, path: Path, proof_format: ProofFormat) -> SatWitness:
        with open(path, "r") as f:
            smt_text = f.read()
        return cls(smt_text, proof_format)

    def serialize(self, path: Path) -> None:
        """Serialize the UNSAT witness to a file."""
        with open(path, "w") as f:
            f.write(self.text)
        
    def serialize_to_string(self) -> str:
        """Serialize the UNSAT witness to a string."""
        return self.text


class Status(str, Enum):
    """Outcome of solving a CHC system."""

    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"
