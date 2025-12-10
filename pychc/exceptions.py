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
