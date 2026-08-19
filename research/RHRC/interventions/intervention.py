from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Mapping

@dataclass(frozen=True)
class InterventionSpec:
    id: str
    changed_object: str
    held_fixed: tuple[str, ...]
    property_tested: str
    interpretation_boundary: str

@dataclass(frozen=True)
class InterventionResult:
    spec: InterventionSpec
    before: Any
    after: Any


def run(spec: InterventionSpec, state: Mapping[str, Any], mutate: Callable[[dict], None], measure: Callable[[Mapping[str, Any]], Any]) -> InterventionResult:
    before_state = dict(state)
    after_state = dict(state)
    mutate(after_state)
    for key in spec.held_fixed:
        if before_state.get(key) != after_state.get(key):
            raise ValueError(f"held-fixed object changed: {key}")
    return InterventionResult(spec, measure(before_state), measure(after_state))
