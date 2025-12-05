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


class PyCHCInvalidResultException(PyCHCException):
    """
    Exception for invalid objects
    """


class PyCHCSolverException(PyCHCException):
    """
    Exception for solver errors
    """
