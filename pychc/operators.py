from pysmt.fnode import FNode
from pysmt.operators import new_node_type
from pysmt.type_checker import SimpleTypeChecker
from pysmt.oracles import FreeVarsOracle, TheoryOracle, QuantifierOracle, TypesOracle
from pysmt.walkers import handles, IdentityDagWalker, DagWalker

import pysmt.formula
import pysmt.printers
import pysmt.smtlib.printers as smtlib_printers
import pysmt.operators as op
from pysmt.simplifier import Simplifier

from pysmt.typing import INT

# New operator node types for integer arithmetic
MOD = new_node_type(node_str="MOD")
INTDIV = new_node_type(node_str="INTDIV")


class FormulaManager(pysmt.formula.FormulaManager):
    """Extend PySMT FormulaManager with integer `mod` operator."""

    def Mod(self, left: FNode, right: FNode) -> FNode:
        return self.create_node(node_type=MOD, args=(left, right))

    def IntDiv(self, left: FNode, right: FNode) -> FNode:
        return self.create_node(node_type=INTDIV, args=(left, right))


# Type checkers


def _type_walk_mod(self, formula, args, **kwargs):
    # Both args must be INT; return INT
    return self.walk_type_to_type(formula, args, INT, INT)


SimpleTypeChecker.set_handler(_type_walk_mod, MOD)


def _type_walk_intdiv(self, formula, args, **kwargs):
    # Both args must be INT; return INT
    return self.walk_type_to_type(formula, args, INT, INT)


SimpleTypeChecker.set_handler(_type_walk_intdiv, INTDIV)

TheoryOracle.set_handler(TheoryOracle.walk_combine, MOD)
QuantifierOracle.set_handler(DagWalker.walk_all, MOD)
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, MOD)
TypesOracle.set_handler(TypesOracle.walk_combine, MOD)

TheoryOracle.set_handler(TheoryOracle.walk_combine, INTDIV)
QuantifierOracle.set_handler(DagWalker.walk_all, INTDIV)
FreeVarsOracle.set_handler(FreeVarsOracle.walk_simple_args, INTDIV)
TypesOracle.set_handler(TypesOracle.walk_combine, INTDIV)

# Printers


def _hr_walk_mod(self, formula):
    return self.walk_nary(formula, " mod ")


pysmt.printers.HRPrinter.set_handler(_hr_walk_mod, MOD)


def _smt_walk_mod(self, formula):
    return self.walk_nary(formula, "mod")


smtlib_printers.SmtPrinter.set_handler(_smt_walk_mod, MOD)


def _smt_dag_walk_mod(self, formula, args):
    return self.walk_nary(formula, args, "mod")


smtlib_printers.SmtDagPrinter.set_handler(_smt_dag_walk_mod, MOD)

# DagWalkers


def _walk_mod(self, formula, args, **kwargs):
    return self.mgr.Mod(args[0], args[1])


IdentityDagWalker.set_handler(_walk_mod, MOD)


# INTDIV printers and walkers
def _hr_walk_intdiv(self, formula):
    return self.walk_nary(formula, " div ")


pysmt.printers.HRPrinter.set_handler(_hr_walk_intdiv, INTDIV)


def _smt_walk_intdiv(self, formula):
    return self.walk_nary(formula, "div")


smtlib_printers.SmtPrinter.set_handler(_smt_walk_intdiv, INTDIV)


def _smt_dag_walk_intdiv(self, formula, args):
    return self.walk_nary(formula, args, "div")


smtlib_printers.SmtDagPrinter.set_handler(_smt_dag_walk_intdiv, INTDIV)


def _walk_intdiv(self, formula, args, **kwargs):
    return self.mgr.IntDiv(args[0], args[1])


IdentityDagWalker.set_handler(_walk_intdiv, INTDIV)

# Simplifier


def _simplifier_walk_mod(self, formula, args, **kwargs):
    # Do not simplify: just rebuild the same MOD node
    return self.manager.Mod(args[0], args[1])


Simplifier.set_handler(_simplifier_walk_mod, MOD)


def _simplifier_walk_intdiv(self, formula, args, **kwargs):
    # Do not simplify: just rebuild the same INTDIV node
    return self.manager.IntDiv(args[0], args[1])


Simplifier.set_handler(_simplifier_walk_intdiv, INTDIV)
