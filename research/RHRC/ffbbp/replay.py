from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, Sequence, TypeVar

T = TypeVar("T")

@dataclass(frozen=True)
class FrozenSplit(Generic[T]):
    calibration: tuple[T, ...]
    validation: tuple[T, ...]
    lockbox: tuple[T, ...]


def deterministic_split(items: Sequence[T], calibration_fraction: float = 0.5, validation_fraction: float = 0.25) -> FrozenSplit[T]:
    if not 0 < calibration_fraction < 1:
        raise ValueError("calibration fraction must be in (0,1)")
    if not 0 < validation_fraction < 1 or calibration_fraction + validation_fraction >= 1:
        raise ValueError("invalid validation fraction")
    n = len(items)
    i = int(n * calibration_fraction)
    j = int(n * (calibration_fraction + validation_fraction))
    return FrozenSplit(tuple(items[:i]), tuple(items[i:j]), tuple(items[j:]))


def assert_lockbox_disjoint(split: FrozenSplit[object]) -> None:
    cal = set(split.calibration)
    val = set(split.validation)
    lock = set(split.lockbox)
    if cal & val or cal & lock or val & lock:
        raise ValueError("calibration/validation/lockbox overlap")
