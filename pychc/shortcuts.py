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

from __future__ import annotations

from pathlib import Path
from typing import Optional

from pysmt.fnode import FNode
from pysmt.shortcuts import Function, Symbol
from pysmt.environment import get_env
from pysmt.typing import BOOL, FunctionType, PySMTType

from pychc.exceptions import PyCHCInvalidSystemException


def Predicate(name: str, arg_types: list[PySMTType]) -> FNode:
    """
    A predicate is a function symbol returning Bool with the given argument types.
    """

    return Symbol(name, FunctionType(BOOL, arg_types))


def Apply(pred: FNode, args: list[FNode]) -> FNode:
    """
    Apply a predicate predicate name to a list of arguments.

    :param pred: a pysmt FNode representing a predicate (i.e., a function symbol
                 with Boolean return type)
    :param args: a list of pysmt FNode representing the arguments
    :return: a pysmt FNode representing the application of the predicate to the arguments
    """

    if not args:
        return pred
    try:
        return Function(pred, args)
    except Exception as e:
        raise PyCHCInvalidSystemException(
            f"Error applying predicate {pred} to arguments {args}: {e}"
        ) from e


def Clause(body: Optional[FNode] = None, head: FNode = None) -> FNode:
    """
    Create a CHC clause from a head and an optional body.

    :param head: a pysmt FNode representing the head of the clause
    :param body: a pysmt FNode representing the body of the clause (optional)
     if not provided, the body is assumed to be TRUE
    :return: a pysmt FNode representing the CHC clause
    """
    from pysmt.shortcuts import Implies, TRUE

    if not body:
        return head
    return Implies(body, head)


def Mod(left: FNode, right: FNode) -> FNode:
    """
    Integer modulus operator shortcut.
    """
    return get_env().formula_manager.Mod(left, right)


def IntDiv(left: FNode, right: FNode) -> FNode:
    """
    Integer division operator shortcut (SMT-LIB: div).
    """
    return get_env().formula_manager.IntDiv(left, right)


class SMTLibFormula(FNode):

    @classmethod
    def load_from_file(cls, file_path: Path) -> FNode:
        """
        Load a formula from an SMT-LIBv2 file.

        :param file_path: path to the SMT-LIBv2 file
        :return: the asserted formula in the file
        """
        from pychc.parser import CHCSmtLibParser

        parser = CHCSmtLibParser()
        script = parser.get_script_fname(str(file_path))
        return script.get_last_formula()
