from __future__ import annotations

from dataclasses import dataclass

@dataclass(frozen=True)
class CommutationResult:
    fast_score: float
    truth_score: float
    absolute_mismatch: float
    relative_mismatch: float
    passed: bool


def assess(fast_score: float, truth_score: float, *, scale: float, absolute_max: float, relative_max: float) -> CommutationResult:
    if scale <= 0:
        raise ValueError("scale must be positive")
    absolute = abs(fast_score - truth_score)
    relative = absolute / scale
    return CommutationResult(fast_score, truth_score, absolute, relative,
                             absolute <= absolute_max and relative <= relative_max)
