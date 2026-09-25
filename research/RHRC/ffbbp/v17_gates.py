from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from ffbbp.v17_contracts import GateStatus, TypedGateResult, required_gate_satisfied


@dataclass(frozen=True)
class AssuranceGateResult:
    status: GateStatus
    blockers: tuple[str, ...]

    @property
    def passed(self) -> bool:
        return self.status is GateStatus.PASS


def reduction_assurance_gate(
    *,
    required_results: Iterable[TypedGateResult],
    structurally_inapplicable: Iterable[str] = (),
) -> AssuranceGateResult:
    """FFBBP 1.7 fail-closed assurance aggregation.

    Required surfaces must be explicit TypedGateResult records. A missing result
    cannot be silently represented as NOT_APPLICABLE; protocol-scoped structural
    nonapplicability is carried separately.
    """
    blockers: list[str] = []
    results = tuple(required_results)
    keys = [r.key for r in results]
    if len(keys) != len(set(keys)):
        return AssuranceGateResult(GateStatus.FAIL, ("DUPLICATE_GATE_KEY",))
    for result in results:
        result.validate()
        if result.status is GateStatus.FAIL:
            blockers.append(f"{result.key}:FAIL")
        elif result.status is GateStatus.NOT_EVALUATED:
            blockers.append(f"{result.key}:NOT_EVALUATED")
        elif result.status is GateStatus.NOT_APPLICABLE:
            blockers.append(f"{result.key}:REQUIRED_GATE_CANNOT_BE_NOT_APPLICABLE")
        elif not required_gate_satisfied(result):
            blockers.append(f"{result.key}:UNSATISFIED")
    for key in structurally_inapplicable:
        if not isinstance(key, str) or not key.strip():
            blockers.append("INVALID_STRUCTURAL_NONAPPLICABILITY")
    status = GateStatus.PASS if not blockers else GateStatus.FAIL
    return AssuranceGateResult(status, tuple(blockers))
