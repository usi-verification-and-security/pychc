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
