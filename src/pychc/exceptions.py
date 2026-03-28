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


class PyCHCException(Exception):
    """
    Base exception for pyvmt
    """


class PyCHCNotImplementedException(PyCHCException):
    """
    Exception for not implemented features
    """


class PyCHCInternalException(PyCHCException):
    """
    Exception for internal errors
    """


class PyCHCInvalidSystemException(PyCHCException):
    """
    Exception for invalid CHC systems

    """


class PyCHCInvalidResultException(PyCHCException):
    """
    Exception for invalid objects

    """


class PyCHCSolverException(PyCHCException):
    """
    Exception for solver errors
    """


class PyCHCUnknownResultException(PyCHCException):
    """
    Exception for unknown solver results
    """
