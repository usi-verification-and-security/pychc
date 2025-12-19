from pychc.environment import reset_env
from pysmt.environment import get_env  # re-export for convenience

# Ensure pyCHC environment (with `mod`) is active upon import
reset_env()
