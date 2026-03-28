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

from pysmt.environment import Environment as PysmtEnvironment, pop_env
from pysmt.environment import get_env, push_env as pysmt_push_env
from pychc.operators import FormulaManager


class Environment(PysmtEnvironment):
    """Extension of pySMT environment for pyCHC to support `mod`."""

    FormulaManagerClass = FormulaManager


def push_env(env=None):
    """Overload push_env to default to pyCHC Environment."""
    if env is None:
        env = Environment()
    return pysmt_push_env(env=env)


def reset_env():
    pop_env()
    push_env()
    return get_env()


# Initialize default environment
reset_env()
