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

import functools
import os
from pathlib import Path

from dotenv import load_dotenv
from pychc.solvers.cvc5 import CVC5Solver
from pychc.solvers.eldarica import EldaricaSolver
from pychc.solvers.golem import GolemSolver
from pychc.solvers.opensmt import OpenSMTSolver
from pychc.solvers.z3 import Z3CHCSolver, Z3SMTSolver

def reset_pysmt_env(test_func):
    @functools.wraps(test_func)
    def _wrapper(*args, **kwargs):
        from pychc.environment import reset_env

        reset_env()
        return test_func(*args, **kwargs)

    return _wrapper


env = load_dotenv(".env.test", override=True, interpolate=True)

cvc5_1_0_5_home = Path(os.environ["CVC5_1_0_5_HOME"])
golem_0_4_0_home = Path(os.environ["GOLEM_0_4_0_HOME"])
eldarica_2_0_9_home = Path(os.environ["ELDARICA_2_0_9_HOME"])
opensmt_2_5_0_home = Path(os.environ["OPENSMT_2_5_0_HOME"])
cvc5_home = Path(os.environ["CVC5_HOME"])
golem_home = Path(os.environ["GOLEM_HOME"])
eldarica_home = Path(os.environ["ELDARICA_HOME"])
opensmt_home = Path(os.environ["OPENSMT_HOME"])
z3_home = Path(os.environ["Z3_HOME"])

def golem_solver(**kwargs):
    return GolemSolver(binary_path=golem_home, **kwargs)

def old_golem_solver(**kwargs):
    return GolemSolver(binary_path=golem_0_4_0_home, **kwargs)

def eldarica_solver(**kwargs):
    return EldaricaSolver(binary_path=eldarica_home, **kwargs)

def old_eldarica_solver(**kwargs):
    return EldaricaSolver(binary_path=eldarica_2_0_9_home, **kwargs)

def opensmt_solver(**kwargs):
    return OpenSMTSolver(binary_path=opensmt_home, **kwargs)

def old_opensmt_solver(**kwargs):
    return OpenSMTSolver(binary_path=opensmt_2_5_0_home, **kwargs)

def cvc5_solver(**kwargs):
    return CVC5Solver(binary_path=cvc5_home, **kwargs)

def old_cvc5_solver(**kwargs):
    return CVC5Solver(binary_path=cvc5_1_0_5_home, **kwargs)

def z3_chc_solver(**kwargs):
    return Z3CHCSolver(binary_path=z3_home, **kwargs)

def z3_smt_solver(**kwargs):
    return Z3SMTSolver(binary_path=z3_home, **kwargs)
