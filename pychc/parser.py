from pathlib import Path
from pysmt.smtlib.parser import SmtLibParser, SmtLibCommand, warn
from pysmt.exceptions import UndefinedLogicError
from pysmt.logics import get_logic_by_name

from pychc.solvers.witness import Status
from pychc.exceptions import PyCHCSolverException, PyCHCUnknownResultException


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


def scan_commands_in_smtlib_file(file: Path) -> list[str]:
    """
    Split an SMT-LIB file into command strings.
    """
    with file.open("r", encoding="utf-8") as f:
        text = f.read()
    return scan_commands(text)


def scan_commands(text: str) -> list[str]:
    commands: list[str] = []
    buf: list[str] = []
    depth = 0
    in_comment = False
    for ch in text:
        # Start a new comment
        if ch == ";":
            in_comment = True
            continue
        # Ignore comments
        if in_comment:
            if ch == "\n":  # End of comment
                in_comment = False
            continue
        if depth == 0 and ch != "(":  # outside command, ignore
            continue
        # Copy verbatim. Track parentheses depth.
        if ch == "(":
            depth += 1
        if ch == ")":
            depth -= 1
        buf.append(ch)
        if depth == 0:  # end of command
            commands.append("".join(buf))
            buf = []

    def clean(cmd: str) -> str:
        new_cmd = cmd.strip().replace("\n", " ")
        cmd = None
        while cmd != new_cmd:
            cmd = new_cmd
            new_cmd = cmd.replace("  ", " ")
        return cmd.replace("( ", "(").replace(" )", ")")

    commands = list(map(clean, commands))
    assert all(cmd for cmd in commands)
    assert all(cmd.startswith("(") and cmd.endswith(")") for cmd in commands)
    return commands


def decide_result(text: str) -> tuple[Status, str]:
    """
    Decide the solving result (SAT/UNSAT/UNKNOWN) from first line.
    Returns the status and the remaining output.
    If first line is not sat/unsat/unknown, raises PyCHCUnknownResultException.
    """
    # status is first line, the rest is self._raw_output
    status, *rest = text.splitlines()
    if status == "sat":
        s = Status.SAT
        # also try to remove open-close brackets
        if len(rest) > 1 and rest[0].strip() == "(" and rest[-1].strip() == ")":
            rest = rest[1:-1]
    elif status == "unsat":
        s = Status.UNSAT
    elif status == "unknown":
        s = Status.UNKNOWN
    else:
        if "error" in text:
            raise PyCHCSolverException(f"Solver reported an error: {text}")
        raise PyCHCUnknownResultException(
            f"Could not understand solver output status: {text}"
        )
    out = "\n".join(rest).strip()
    return s, out
