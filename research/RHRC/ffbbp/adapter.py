from __future__ import annotations

from dataclasses import dataclass
from math import sqrt
from statistics import mean
from typing import Iterable, Sequence

@dataclass(frozen=True)
class Observation:
    source: tuple[float, ...]
    target: float | None = None

@dataclass(frozen=True)
class Association:
    nearest_index: int
    distance: float


def euclidean(a: Sequence[float], b: Sequence[float]) -> float:
    if len(a) != len(b):
        raise ValueError("dimension mismatch")
    return sqrt(sum((x-y) ** 2 for x, y in zip(a, b)))


def associate_source_only(observation: Observation, prototypes: Sequence[Sequence[float]]) -> Association:
    """Certificate association: source-only by construction. Target is never read."""
    if not prototypes:
        raise ValueError("prototypes required")
    scored = [(euclidean(observation.source, p), i) for i, p in enumerate(prototypes)]
    dist, idx = min(scored)
    return Association(idx, dist)


def zero_field_rmse(targets: Iterable[float]) -> float:
    vals = list(targets)
    if not vals:
        raise ValueError("targets required")
    return sqrt(mean(v * v for v in vals))


def rmse(targets: Sequence[float], predictions: Sequence[float]) -> float:
    if len(targets) != len(predictions) or not targets:
        raise ValueError("equal nonempty inputs required")
    return sqrt(mean((a-b) ** 2 for a, b in zip(targets, predictions)))


def lift_vs_null(candidate_rmse: float, null_rmse: float) -> float:
    if null_rmse <= 0:
        raise ValueError("null_rmse must be positive")
    return (null_rmse - candidate_rmse) / null_rmse
