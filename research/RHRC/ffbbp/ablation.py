from __future__ import annotations

from dataclasses import dataclass

@dataclass(frozen=True)
class AblationResult:
    baseline_rmse: float
    ablated_rmse: float
    degradation: float
    passed: bool


def candidate_aligned_ablation(baseline_rmse: float, ablated_rmse: float, *, min_degradation: float = 0.0) -> AblationResult:
    if baseline_rmse < 0 or ablated_rmse < 0:
        raise ValueError("RMSE must be nonnegative")
    degradation = ablated_rmse - baseline_rmse
    return AblationResult(baseline_rmse, ablated_rmse, degradation, degradation > min_degradation)
