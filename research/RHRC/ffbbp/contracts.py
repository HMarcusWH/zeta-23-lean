from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import math
from typing import Iterable, Sequence


class EvidencePartition(str, Enum):
    TRAIN = "TRAIN"
    SELECT = "SELECT"
    CONFIRM = "CONFIRM"
    AUDIT = "AUDIT"


class RunPhase(str, Enum):
    TRAIN = "TRAIN"
    SELECT = "SELECT"
    CONFIRM = "CONFIRM"
    UNKNOWN_DIAGNOSTIC = "UNKNOWN_DIAGNOSTIC"
    PILOT = "PILOT"


class FidelityMode(str, Enum):
    FAST = "FAST"
    HYBRID = "HYBRID"
    REFERENCE = "REFERENCE"


@dataclass(frozen=True)
class InformationPartition:
    train_ids: frozenset[str]
    select_ids: frozenset[str]
    confirm_ids: frozenset[str]
    audit_ids: frozenset[str]

    def validate(self) -> None:
        groups = {
            EvidencePartition.TRAIN: self.train_ids,
            EvidencePartition.SELECT: self.select_ids,
            EvidencePartition.CONFIRM: self.confirm_ids,
            EvidencePartition.AUDIT: self.audit_ids,
        }
        keys = list(groups)
        for i, a in enumerate(keys):
            for b in keys[i + 1 :]:
                overlap = groups[a] & groups[b]
                if overlap:
                    raise ValueError(f"partition overlap {a.value}/{b.value}: {sorted(overlap)!r}")

    @property
    def build_ids(self) -> frozenset[str]:
        return self.train_ids | self.select_ids

    def construction_allowed(self, sample_id: str) -> bool:
        return sample_id in self.build_ids

    def confirm_feedback_allowed(self) -> bool:
        return False


def lift_validation(model_rmse: float, zero_rmse: float) -> float:
    """RUN42B definition, evaluated before existence shrinkage."""
    if not math.isfinite(model_rmse) or not math.isfinite(zero_rmse) or zero_rmse <= 0:
        raise ValueError("RMSE inputs must be finite and zero_rmse > 0")
    return 1.0 - model_rmse / zero_rmse


def existence_weight(lift: float, *, tau: float, slope: float) -> float:
    x = slope * (lift - tau)
    if x >= 0:
        z = math.exp(-x)
        return 1.0 / (1.0 + z)
    z = math.exp(x)
    return z / (1.0 + z)


def certificate_shrink(raw_value: float, *, weight: float, minimum_shrink: float) -> float:
    if not (0.0 <= weight <= 1.0):
        raise ValueError("weight must be in [0,1]")
    if not (0.0 <= minimum_shrink <= 1.0):
        raise ValueError("minimum_shrink must be in [0,1]")
    return (minimum_shrink + (1.0 - minimum_shrink) * weight) * raw_value


def masked_renormalized_distance_sq(
    a: Sequence[float | None],
    b: Sequence[float | None],
    scales: Sequence[float],
    lengthscales: Sequence[float],
    *,
    softclip: float,
    min_overlap_fraction: float = 0.5,
) -> float:
    if not (len(a) == len(b) == len(scales) == len(lengthscales)):
        raise ValueError("all feature arrays must have the same length")
    p = len(a)
    if p == 0:
        raise ValueError("empty feature vectors")
    observed: list[int] = []
    for k, (x, y) in enumerate(zip(a, b)):
        if x is None or y is None:
            continue
        if not (math.isfinite(float(x)) and math.isfinite(float(y))):
            continue
        observed.append(k)
    required = max(1, math.ceil(min_overlap_fraction * p))
    if len(observed) < required:
        raise ValueError("insufficient shared observed coordinates")
    total = 0.0
    for k in observed:
        sigma = float(scales[k])
        ell = float(lengthscales[k])
        if sigma <= 0 or ell <= 0:
            raise ValueError("scales and ARD lengthscales must be positive")
        d = (float(a[k]) - float(b[k])) / sigma
        clipped = softclip * math.tanh(d / softclip)
        total += (clipped / ell) ** 2
    return (p / len(observed)) * total


@dataclass(frozen=True)
class RefitSemantics:
    protocol_frozen: bool = True
    preprocessing_policy_frozen: bool = True
    hyperparameters_frozen: bool = True
    family_selection_rule_frozen: bool = True
    evaluation_surfaces_frozen: bool = True
    ordinary_train_parameters_refit: bool = True

    def validate(self) -> None:
        fixed = (
            self.protocol_frozen,
            self.preprocessing_policy_frozen,
            self.hyperparameters_frozen,
            self.family_selection_rule_frozen,
            self.evaluation_surfaces_frozen,
            self.ordinary_train_parameters_refit,
        )
        if not all(fixed):
            raise ValueError("RHRC reference ablation/null semantics require frozen protocol surfaces and TRAIN refit")


@dataclass(frozen=True)
class KnockoffRecord:
    preserved: tuple[str, ...]
    destroyed: tuple[str, ...]
    generated_from_partition: EvidencePartition
    refit_semantics: RefitSemantics
    seed: int

    def validate(self) -> None:
        if not self.preserved or not self.destroyed:
            raise ValueError("knockoff must declare preserved and destroyed structure")
        if self.generated_from_partition is EvidencePartition.CONFIRM:
            raise ValueError("confirm/lockbox data may not generate a knockoff construction")
        self.refit_semantics.validate()


@dataclass(frozen=True)
class QualificationKey:
    core_profile_id: str
    domain_adapter_id: str

    def __str__(self) -> str:
        return f"{self.core_profile_id}::{self.domain_adapter_id}"
