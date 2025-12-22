from __future__ import annotations

from typing import Optional

from pychc.solvers.proof_checker import ProofChecker, ProofCheckerOptions
from pychc.solvers.witness import ProofFormat


class CarcaraOptions(ProofCheckerOptions):
    """
    Default options for Carcara invocation.
    """

    def __init__(self, **base_options):
        super().__init__(**base_options)
        self.set_mode("check")
        self.set_flag("--ignore-unknown-rules", True)
        self.set_flag("--allow-int-real-subtyping", True)
        self.set_flag("--expand-let-bindings", True)


class Carcara(ProofChecker):
    """
    Carcara proof checker interface.
    """

    NAME = "carcara"
    OPTION_CLASS = CarcaraOptions

    def get_proof_format(self) -> Optional[ProofFormat]:
        return ProofFormat.ALETHE

    def _decide_result(self) -> bool:
        # TODO: check this...
        return self._raw_output in {"holey", "valid"}
