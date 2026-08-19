from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

@dataclass(frozen=True)
class TransferResult:
    lifts: Mapping[str, float | None]
    required: tuple[str, ...]
    blockers: tuple[str, ...]
    passed: bool


def require_positive_lift(lifts: Mapping[str, float | None], required: tuple[str, ...]) -> TransferResult:
    blockers: list[str] = []
    for name in required:
        value = lifts.get(name)
        if value is None:
            blockers.append(f"{name}:INSUFFICIENT_ROWS")
        elif value <= 0:
            blockers.append(f"{name}:NONPOSITIVE_LIFT")
    return TransferResult(dict(lifts), required, tuple(blockers), not blockers)
