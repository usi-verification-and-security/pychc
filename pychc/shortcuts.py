from __future__ import annotations

from typing import Optional

from pysmt.fnode import FNode
from pysmt.shortcuts import Function, Symbol
from pysmt.typing import BOOL, FunctionType, PySMTType

from pychc.exceptions import PyCHCInvalidSystemException


def Predicate(name: str, arg_types: list[PySMTType]) -> FNode:
    """
    A predicate is a function symbol returning Bool with the given argument types.
    """

    if not arg_types:
        raise PyCHCInvalidSystemException(
            "Predicate must have at least one argument type"
        )
    return Symbol(name, FunctionType(BOOL, arg_types))


def Apply(pred: FNode, args: list[FNode]) -> FNode:
    """
    Apply a predicate predicate name to a list of arguments.

    :param pred: a pysmt FNode representing a predicate (i.e., a function symbol
                 with Boolean return type)
    :param args: a list of pysmt FNode representing the arguments
    :return: a pysmt FNode representing the application of the predicate to the arguments
    """

    try:
        return Function(pred, args)
    except Exception as e:
        raise PyCHCInvalidSystemException(
            f"Error applying predicate {pred} to arguments {args}: {e}"
        ) from e
