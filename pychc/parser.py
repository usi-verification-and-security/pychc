import functools

from pysmt.smtlib.parser import SmtLibParser
from pysmt.fnode import FNode


class CHCSmtLibParser(SmtLibParser):
    """Custom SMT-LIB parser with LIA symbols."""

    def __init__(self, *args, predicates: set[FNode] = set(), **kwargs):
        self.predicates = predicates
        super().__init__(*args, **kwargs)

        # add support for `div` and `mod` operators
        mgr = self.env.formula_manager
        self.interpreted["div"] = self._operator_adapter(mgr.IntDiv)
        self.interpreted["mod"] = self._operator_adapter(mgr.Mod)

    def _reset(self):
        super()._reset()
        for pred in self.predicates:
            self._declare_predicate(pred)

    def _declare_predicate(self, pred: FNode):
        if pred.get_type().is_function_type():
            self.cache.bind(
                pred.symbol_name(), functools.partial(self._function_call_helper, pred)
            )
        else:
            self.cache.bind(pred.symbol_name(), pred)
