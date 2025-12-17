from pysmt.smtlib.parser import SmtLibParser
from pysmt.typing import FunctionType, INT


class CHCParser(SmtLibParser):
    """Custom SMT-LIB parser for CHC systems."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        mgr = self.env.formula_manager

        mod = mgr.Symbol("mod", FunctionType(INT, [INT, INT]))

        def _mk_mod(*args):
            return mgr.Function(mod, list(args))

        self.interpreted["div"] = self._operator_adapter(mgr.Div)
        self.interpreted["mod"] = self._operator_adapter(_mk_mod)
