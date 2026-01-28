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
