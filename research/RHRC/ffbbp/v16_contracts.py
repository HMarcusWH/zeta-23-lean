from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import math
import re
from typing import Mapping


_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def _nonempty(value: str, label: str) -> None:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label} must be a nonempty string")


def _sha256(value: str, label: str) -> None:
    if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
        raise ValueError(f"{label} must be a lowercase sha256 hex digest")


class XiMode(str, Enum):
    SNAPSHOT = "SNAPSHOT"
    STATEFUL = "STATEFUL"


class MaskingStatus(str, Enum):
    CLEARED = "CLEARED"
    UNRESOLVED = "UNRESOLVED"
    FAILED = "FAILED"


@dataclass(frozen=True)
class XiReductionContract:
    """FFBBP v1.6 Xi reduction contract.

    This mirrors the paper-level typed reduction surface.  A mandatory inverse
    is intentionally absent because many lawful reductions are many-to-one.
    """

    reduction_id: str
    xi_mode: XiMode
    source_state_schema: str
    xi_schema: str
    reduction_map_version: str
    reference_path_id: str
    diagnostic_map_id: str
    decision_map_id: str
    metric_refs: tuple[str, ...]
    clock_contract_refs: tuple[str, ...]
    trust_region: Mapping[str, object]
    claim_cap_ref: str
    provenance_hash: str

    def validate(self) -> None:
        for label, value in (
            ("reduction_id", self.reduction_id),
            ("source_state_schema", self.source_state_schema),
            ("xi_schema", self.xi_schema),
            ("reduction_map_version", self.reduction_map_version),
            ("reference_path_id", self.reference_path_id),
            ("diagnostic_map_id", self.diagnostic_map_id),
            ("decision_map_id", self.decision_map_id),
            ("claim_cap_ref", self.claim_cap_ref),
        ):
            _nonempty(value, label)
        if not isinstance(self.xi_mode, XiMode):
            raise ValueError("xi_mode must be XiMode")
        if not self.metric_refs or not all(isinstance(x, str) and x.strip() for x in self.metric_refs):
            raise ValueError("metric_refs must contain nonempty strings")
        if not self.clock_contract_refs or not all(
            isinstance(x, str) and x.strip() for x in self.clock_contract_refs
        ):
            raise ValueError("clock_contract_refs must contain nonempty strings")
        if not isinstance(self.trust_region, Mapping) or not self.trust_region:
            raise ValueError("trust_region must be a nonempty mapping")
        _sha256(self.provenance_hash, "provenance_hash")


@dataclass(frozen=True)
class ResidualRecord:
    """Typed FFBBP v1.6 residual.

    The value may be scalar or structured, but its spaces, metric, units,
    clock, trust region and hard/soft semantics may not be erased.
    """

    residual_id: str
    semantic_type: str
    source_space: str
    target_space: str
    metric_id: str
    normalization_id: str | None
    units: str
    clock_basis: str
    trust_region: Mapping[str, object]
    sensitivity_map_ref: str | None
    value: float | Mapping[str, object]
    uncertainty: Mapping[str, object] | None
    hard_gate: bool
    provenance_hash: str

    def validate(self) -> None:
        for label, value in (
            ("residual_id", self.residual_id),
            ("semantic_type", self.semantic_type),
            ("source_space", self.source_space),
            ("target_space", self.target_space),
            ("metric_id", self.metric_id),
            ("units", self.units),
            ("clock_basis", self.clock_basis),
        ):
            _nonempty(value, label)
        if self.normalization_id is not None:
            _nonempty(self.normalization_id, "normalization_id")
        if self.sensitivity_map_ref is not None:
            _nonempty(self.sensitivity_map_ref, "sensitivity_map_ref")
        if not isinstance(self.trust_region, Mapping) or not self.trust_region:
            raise ValueError("trust_region must be a nonempty mapping")
        if isinstance(self.value, (int, float)):
            if not math.isfinite(float(self.value)):
                raise ValueError("scalar residual value must be finite")
        elif not isinstance(self.value, Mapping):
            raise ValueError("residual value must be finite scalar or structured mapping")
        if self.uncertainty is not None and not isinstance(self.uncertainty, Mapping):
            raise ValueError("uncertainty must be a mapping or None")
        if not isinstance(self.hard_gate, bool):
            raise ValueError("hard_gate must be bool")
        _sha256(self.provenance_hash, "provenance_hash")


@dataclass(frozen=True)
class ClockMapRecord:
    source_clock: str
    target_clock: str
    map_version: str
    orientation: str
    domain: Mapping[str, object]
    endpoints: Mapping[str, object]
    jacobian_rule: Mapping[str, object]
    uncertainty: Mapping[str, object]
    valid_from: str | None
    expiry: str | None
    provenance_hash: str

    def validate(self) -> None:
        for label, value in (
            ("source_clock", self.source_clock),
            ("target_clock", self.target_clock),
            ("map_version", self.map_version),
        ):
            _nonempty(value, label)
        if self.orientation not in {"increasing", "decreasing"}:
            raise ValueError("orientation must be increasing or decreasing")
        for label, value in (
            ("domain", self.domain),
            ("endpoints", self.endpoints),
            ("jacobian_rule", self.jacobian_rule),
            ("uncertainty", self.uncertainty),
        ):
            if not isinstance(value, Mapping):
                raise ValueError(f"{label} must be a mapping")
        _sha256(self.provenance_hash, "provenance_hash")


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
