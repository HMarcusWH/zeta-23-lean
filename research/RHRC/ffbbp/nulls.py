from __future__ import annotations

from dataclasses import dataclass
from statistics import mean

@dataclass(frozen=True)
class NullEnsembleResult:
    amplitudes: tuple[float, ...]
    mean_amplitude: float
    max_amplitude: float
    passed: bool


def assess_known_null(amplitudes, *, mean_max: float, individual_max: float) -> NullEnsembleResult:
    vals = tuple(float(x) for x in amplitudes)
    if not vals:
        raise ValueError("null amplitudes required")
    m = mean(vals)
    mx = max(vals)
    return NullEnsembleResult(vals, m, mx, m <= mean_max and mx <= individual_max)
