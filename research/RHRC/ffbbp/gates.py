from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

@dataclass(frozen=True)
class GateResult:
    passed: bool
    blockers: tuple[str, ...]


def collapse_gate(*, candidate_rmse: float, null_rmses: Mapping[str, float],
                  known_null_pass: bool, firewall_pass: bool,
                  ablation_pass: bool, transfer_pass: bool,
                  commutation_pass: bool) -> GateResult:
    blockers: list[str] = []
    if not null_rmses:
        blockers.append("NO_LEGAL_NULLS")
    elif candidate_rmse >= min(null_rmses.values()):
        blockers.append("BEST_NULL_NOT_BEATEN")
    if not known_null_pass:
        blockers.append("KNOWN_NULL_FAIL")
    if not firewall_pass:
        blockers.append("SOURCE_TARGET_FIREWALL_FAIL")
    if not ablation_pass:
        blockers.append("CANDIDATE_ALIGNED_ABLATION_FAIL")
    if not transfer_pass:
        blockers.append("TRANSFER_FAIL")
    if not commutation_pass:
        blockers.append("COMMUTATION_FAIL")
    return GateResult(not blockers, tuple(blockers))
