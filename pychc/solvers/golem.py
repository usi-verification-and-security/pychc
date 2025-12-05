"""
Golem instance of CHCSolver
"""

from __future__ import annotations

import tempfile
import logging

from pathlib import Path
from subprocess import run, CalledProcessError

from typing import Optional

from pysmt.substituter import FunctionInterpretation
from pysmt.smtlib.parser.parser import SmtLibParser
from pysmt.typing import BOOL

from pychc.chc_system import CHCSystem
from pychc.solvers.chc_witness import CHCStatus, CHCWitness, SatWitness
from pychc.solvers.chc_solver import CHCSolver
from pychc.exceptions import PyCHCInvalidResultException, PyCHCSolverException


class GolemSolver(CHCSolver):
    """Solver adapter for the Golem CHC solver."""

    NAME = "golem"

    def __init__(self, chc_system: CHCSystem, binary_path: Optional[Path] = None):
        from shutil import which

        super().__init__(chc_system)
        self.options = GolemOptions()

        # Find Golem executable
        if binary_path:
            solver_path = which(GolemSolver.NAME, path=str(binary_path))
        else:
            solver_path = which(GolemSolver.NAME)
        if not solver_path:
            raise PyCHCSolverException(f"Golem executable not found")
        self._solver_path = Path(solver_path)
        if not self._solver_path.is_file():
            raise PyCHCSolverException(
                f"Golem executable not found at: {self._solver_path}"
            )

    def solve(self, get_witness: bool = False) -> CHCStatus:
        """
        Execute Golem on the given CHC system and return the status.
        """

        if get_witness:
            self.options.enable_print_witness(True)

        args_extra = self.options.to_array()

        with tempfile.NamedTemporaryFile("w", suffix=".smt2") as input_path:
            self.system.serialize(Path(input_path.name))
            args = [str(self._solver_path), str(input_path.name)] + args_extra
            try:
                logging.debug(f"Running Golem: {' '.join(args)}")
                proc = run(args, capture_output=True, text=True, check=True)
            except CalledProcessError as err:
                raw_output = (err.stdout or "") + (err.stderr or "")
                logging.error(f"Golem execution failed: {raw_output}")
                self._status = CHCStatus.UNKNOWN
                raise PyCHCSolverException(f"Golem execution failed")

            raw_output = (proc.stdout or "").strip()

            # Understand if SAT/UNSAT/UNKNOWN
            self._status = self.decide_result(raw_output)

            if not get_witness or self._status == CHCStatus.UNKNOWN:
                return self._status

            # Extract witness
            if self._status == CHCStatus.SAT:
                self._witness = self.extract_model(raw_output)
            else:
                self._witness = self.extract_unsat_proof(raw_output)

            return self._status

    def get_witness(self) -> CHCWitness:
        return self._witness

    def decide_result(self, output: str) -> CHCStatus:
        first = output.splitlines()[0].strip().lower() if output else ""
        if first == "sat":
            return CHCStatus.SAT
        if first == "unsat":
            return CHCStatus.UNSAT
        return CHCStatus.UNKNOWN

    def extract_model(self, output: str) -> Optional[SatWitness]:
        """
        Extract a SAT witness (model) from solver output.

        Assumes everything after the first line is SMT-LIB and may contain
        multiple `define-fun`. Stores each definition body as a pysmt formula.
        """
        from io import StringIO

        lines = output.splitlines()
        if not lines:
            return None
        # Skip the first status line, first open and last closed parenthesis
        smt_text = "\n".join(lines[2:-1])
        parser = SmtLibParser()
        script = parser.get_script(StringIO(smt_text))
        predicates = {}
        decls = script.filter_by_command_name(("declare-fun", "define-fun"))
        for decl in decls:
            args = getattr(decl, "args", [])
            if len(args) == 4:
                if args[2] != BOOL:
                    raise PyCHCInvalidResultException("Cannot parse: \n" + smt_text)
                name = args[0]
                interpretation = FunctionInterpretation(
                    formal_params=args[1], function_body=args[3], allow_free_vars=False
                )
                predicates[name] = interpretation
            else:
                logging.warning(f"Skipping malformed declaration? {decl}")

        witness = SatWitness(predicates)
        if not self.system.check_witness_consistency(witness):
            raise PyCHCInvalidResultException(
                "Extracted model is not consistent with the CHC system predicates."
            )

        return witness

    def extract_unsat_proof(self, output: str) -> Optional[UnsatWitness]:
        """Extract an UNSAT certificate/proof from solver output."""

        raise NotImplementedError


class GolemOptions:
    """Options passed to the Golem process via command line flags."""

    def __init__(self):
        self._options = {}
        self._flags = set()

    def enable_print_witness(self, value: bool = True):
        """Enable `--print-witness` to request witness output."""

        self._set_flag("--print-witness", value)

    def to_array(self) -> list[str]:
        """Convert options to CLI args list."""

        res = []
        for opt, val in self._options.items():
            res.append(str(opt))
            res.append(str(val))
        res.extend(self._flags)
        return res

    def _set_flag(self, flag: str, value: bool = True):
        if value:
            self._flags.add(flag)
        else:
            self._flags.discard(flag)
