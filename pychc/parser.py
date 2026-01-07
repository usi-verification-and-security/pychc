from pysmt.smtlib.parser import SmtLibParser, SmtLibCommand, warn
from pysmt.exceptions import UndefinedLogicError
from pysmt.logics import get_logic_by_name


class CHCSmtLibParser(SmtLibParser):
    """Custom SMT-LIB parser with LIA symbols."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        # add support for `div` and `mod` operators
        mgr = self.env.formula_manager
        self.interpreted["div"] = self._operator_adapter(mgr.IntDiv)
        self.interpreted["mod"] = self._operator_adapter(mgr.Mod)

    def _cmd_set_logic(self, current, tokens):
        """(set-logic <symbol>)"""
        elements = self.parse_atoms(tokens, current, 1)
        name = elements[0]
        if name == "HORN":
            # Avoid warnings when reading a HORN logic file
            return SmtLibCommand(current, [None])
        try:
            self.logic = get_logic_by_name(name)
            return SmtLibCommand(current, [self.logic])
        except UndefinedLogicError:
            warn("Unknown logic '" + name + "'. Ignoring set-logic command.")
            return SmtLibCommand(current, [None])
