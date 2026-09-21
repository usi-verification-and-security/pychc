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

import argparse
import logging
import sys
from pathlib import Path

from pysmt.fnode import FNode

from pychc.chc_system import CHCSystem
from pychc.environment import reset_env
from pychc.exceptions import PyCHCException
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.golem import GolemEngines, GolemSolver
from pychc.solvers.opensmt import OpenSMTSolver
from pychc.solvers.z3 import Z3CHCSolver
from pychc.solvers.witness import SatWitness, Status


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run a CHC solver on an SMT-LIB file and optionally validate the result."
    )
    parser.add_argument(
        "solver",
        choices=("eldarica", "z3", "golem"),
        help="CHC solver to use.",
    )
    parser.add_argument(
        "file",
        type=Path,
        help="Path to the SMT-LIB input file.",
    )
    parser.add_argument(
        "--solver-path",
        type=Path,
        default=None,
        help="Path to the CHC solver executable (parent directory or binary path).",
    )
    parser.add_argument(
        "--validator",
        choices=("cvc5", "z3", "opensmt"),
        default=None,
        help="SMT validator to use for validating a SAT witness.",
    )
    parser.add_argument(
        "--validator-path",
        type=Path,
        default=None,
        help="Path to the SMT validator executable (parent directory or binary path).",
    )
    parser.add_argument(
        "--print-witness",
        action="store_true",
        help="Print the produced witness after solving.",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="Enable verbose logging.",
    )
    return parser.parse_args()


def build_solver(name: str, path: Path | None):
    kwargs = {}
    if path is not None:
        kwargs["binary_path"] = path

    if name == "z3":
        return Z3CHCSolver(global_guidance=True, **kwargs)
    if name == "eldarica":
        return EldaricaSolver(**kwargs)
    if name == "golem":
        return GolemSolver(**kwargs)
    raise ValueError(f"Unknown CHC solver: {name}")


def build_validator(name: str, path: Path | None):
    kwargs = {}
    if path is not None:
        kwargs["binary_path"] = path

    if name == "cvc5":
        return CVC5Solver(**kwargs)
    if name == "z3":
        from pychc.solvers.z3 import Z3SMTSolver
        return Z3SMTSolver(**kwargs)
    if name == "opensmt":
        return OpenSMTSolver(**kwargs)
    raise ValueError(f"Unknown validator: {name}")


def main() -> int:
    args = parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(levelname)s: %(message)s",
    )

    reset_env()

    try:
        solver = build_solver(args.solver, args.solver_path)
        status = solver.run(args.file)
        print(f"Result: {status.value}")

        if args.print_witness:
            witness = solver.get_witness()
            if witness is not None:
                print("--- Witness ---")
                if (isinstance(witness, SatWitness)):
                    for var, expr in witness.definitions.items():
                        if (isinstance(expr, FNode)):
                            print(f"{var} := {expr.serialize()}")
                        else:
                            print(f"{var} := {expr.function_body.serialize()}")
                else:
                    print(witness.serialize_to_string())

            else:
                print("No witness available.")

        if status == Status.SAT and args.validator:
            sys = CHCSystem.load_from_file(args.file)
            validator = build_validator(args.validator, args.validator_path)
            sys.validate_sat_model(solver.get_witness(), validator)
            print("SAT witness is valid.")

    except PyCHCException as e:
        logging.error(e)
        return 1
    except Exception as e:
        logging.error(f"Unexpected error: {e}")
        if args.verbose:
            logging.exception(e)
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
