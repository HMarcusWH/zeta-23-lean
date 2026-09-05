from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeVar

T = TypeVar("T")


@dataclass(frozen=True)
class DiagnosticCommutationResult:
    reduced_score: float
    reference_score: float
    absolute_mismatch: float
    relative_mismatch: float
    passed: bool


@dataclass(frozen=True)
class DecisionCommutationResult(Generic[T]):
    reduced_decision: T
    reference_decision: T
    passed: bool


def assess_diagnostic(
    reduced_score: float,
    reference_score: float,
    *,
    scale: float,
    absolute_max: float,
    relative_max: float,
) -> DiagnosticCommutationResult:
    if scale <= 0:
        raise ValueError("scale must be positive")
    if absolute_max < 0 or relative_max < 0:
        raise ValueError("commutation tolerances must be nonnegative")
    absolute = abs(reduced_score - reference_score)
    relative = absolute / scale
    return DiagnosticCommutationResult(
        reduced_score,
        reference_score,
        absolute,
        relative,
        absolute <= absolute_max and relative <= relative_max,
    )


def assess_decision(reduced_decision: T, reference_decision: T) -> DecisionCommutationResult[T]:
    return DecisionCommutationResult(
        reduced_decision,
        reference_decision,
        reduced_decision == reference_decision,
    )
