from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import math


class MaskingStatus(str, Enum):
    CLEARED = "CLEARED"
    UNRESOLVED = "UNRESOLVED"
    FAILED = "FAILED"


@dataclass(frozen=True)
class XiReductionContract:
    reduction_id: str
    source_object: str
    reduced_object: str
    metric: str
    trust_region: str
    claim_cap: str = "diagnostic_only"

    def validate(self) -> None:
        fields = (
            self.reduction_id,
            self.source_object,
            self.reduced_object,
            self.metric,
            self.trust_region,
            self.claim_cap,
        )
        if not all(isinstance(x, str) and x.strip() for x in fields):
            raise ValueError("XiReductionContract fields must be nonempty strings")


@dataclass(frozen=True)
class ResidualRecord:
    residual_id: str
    kind: str
    value: float
    upper_bound: float | None
    metric: str
    provenance: tuple[str, ...]

    def validate(self) -> None:
        if not self.residual_id or not self.kind or not self.metric:
            raise ValueError("residual id/kind/metric must be nonempty")
        if not math.isfinite(self.value) or self.value < 0:
            raise ValueError("residual value must be finite and nonnegative")
        if self.upper_bound is not None:
            if not math.isfinite(self.upper_bound) or self.upper_bound < self.value:
                raise ValueError("upper_bound must be finite and >= value")
        if not self.provenance:
            raise ValueError("residual provenance is required")


@dataclass(frozen=True)
class DefeaterContract:
    defeater_id: str
    statement: str
    test_id: str
    result: bool | None = None

    def validate(self) -> None:
        if not self.defeater_id or not self.statement or not self.test_id:
            raise ValueError("defeater contract must declare id, statement and test")


@dataclass(frozen=True)
class EvidenceNeed:
    need_id: str
    statement: str
    acceptable_sources: tuple[str, ...]
    blocker_if_missing: bool = True

    def validate(self) -> None:
        if not self.need_id or not self.statement or not self.acceptable_sources:
            raise ValueError("evidence need must be explicit and source-bounded")


@dataclass(frozen=True)
class ExplicitWitnessCertificate:
    witness_id: str
    visibility_pass: bool
    margin_lower: float
    perturbation_upper: float
    masking_status: MaskingStatus
    provenance: tuple[str, ...]

    def validate(self) -> None:
        if not self.witness_id or not self.provenance:
            raise ValueError("witness id and provenance are required")
        for name, value in (
            ("margin_lower", self.margin_lower),
            ("perturbation_upper", self.perturbation_upper),
        ):
            if not math.isfinite(value) or value < 0:
                raise ValueError(f"{name} must be finite and nonnegative")

    @property
    def perturbation_safe(self) -> bool:
        return self.margin_lower > self.perturbation_upper

    @property
    def claim_safe(self) -> bool:
        return (
            self.visibility_pass
            and self.perturbation_safe
            and self.masking_status is MaskingStatus.CLEARED
        )
