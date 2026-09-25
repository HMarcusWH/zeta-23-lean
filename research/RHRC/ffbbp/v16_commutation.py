from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from typing import Callable, Generic, Sequence, TypeVar

T = TypeVar("T")
R = TypeVar("R")


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


@dataclass(frozen=True)
class CategoricalFiberCounterexample:
    reduction_key: str
    values: tuple[str, ...]
    member_ids: tuple[str, ...]


@dataclass(frozen=True)
class CategoricalSnapshotSufficiencyResult:
    full_state_count: int
    fiber_count: int
    collision_fiber_count: int
    mixed_value_fiber_count: int
    max_fiber_size: int
    passed: bool
    counterexamples: tuple[CategoricalFiberCounterexample, ...]

    def to_dict(self) -> dict:
        return {
            "full_state_count": self.full_state_count,
            "fiber_count": self.fiber_count,
            "collision_fiber_count": self.collision_fiber_count,
            "mixed_value_fiber_count": self.mixed_value_fiber_count,
            "max_fiber_size": self.max_fiber_size,
            "passed": self.passed,
            "counterexamples": [asdict(row) for row in self.counterexamples],
        }


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


def _stable_key(value: object) -> str:
    try:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    except TypeError:
        return repr(value)


def assess_categorical_snapshot_sufficiency(
    items: Sequence[R],
    *,
    reduction_key: Callable[[R], object],
    value_map: Callable[[R], object],
    item_id: Callable[[R], str],
    max_counterexamples: int = 20,
) -> CategoricalSnapshotSufficiencyResult:
    """Exact fiber test for a snapshot reduction.

    This is the finite current-snapshot version of the FFBBP v1.6 factorization
    condition R(P1)=R(P2) => Cfull(P1)=Cfull(P2).  It certifies only the supplied
    finite snapshot and categorical value map; it is not a theorem about future
    repository states or stateful transition closure.
    """
    if max_counterexamples < 0:
        raise ValueError("max_counterexamples must be nonnegative")

    fibers: dict[str, list[tuple[str, str]]] = {}
    for item in items:
        key = _stable_key(reduction_key(item))
        value = _stable_key(value_map(item))
        ident = item_id(item)
        fibers.setdefault(key, []).append((ident, value))

    collision_fibers = 0
    mixed: list[CategoricalFiberCounterexample] = []
    max_fiber_size = 0
    for key in sorted(fibers):
        members = fibers[key]
        max_fiber_size = max(max_fiber_size, len(members))
        if len(members) > 1:
            collision_fibers += 1
        values = sorted({value for _, value in members})
        if len(values) > 1:
            mixed.append(
                CategoricalFiberCounterexample(
                    reduction_key=key,
                    values=tuple(values),
                    member_ids=tuple(sorted(ident for ident, _ in members)),
                )
            )

    return CategoricalSnapshotSufficiencyResult(
        full_state_count=len(items),
        fiber_count=len(fibers),
        collision_fiber_count=collision_fibers,
        mixed_value_fiber_count=len(mixed),
        max_fiber_size=max_fiber_size,
        passed=not mixed,
        counterexamples=tuple(mixed[:max_counterexamples]),
    )
