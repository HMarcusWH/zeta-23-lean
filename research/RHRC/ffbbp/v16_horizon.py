from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import math


class HorizonStatus(str, Enum):
    HORIZON_CERTIFIED = "HORIZON_CERTIFIED"
    HORIZON_UNSAFE = "HORIZON_UNSAFE"
    HORIZON_BOUND_UNAVAILABLE = "HORIZON_BOUND_UNAVAILABLE"
    OUTSIDE_TRUST_REGION = "OUTSIDE_TRUST_REGION"


@dataclass(frozen=True)
class ResidualHorizonContract:
    model_class: str
    local_defect_upper: float
    sensitivity_upper: float | None
    requested_horizon: float
    target_metric: str
    trust_region: str

    def validate(self) -> None:
        if not self.model_class or not self.target_metric or not self.trust_region:
            raise ValueError("model class, target metric and trust region are required")
        if not math.isfinite(self.local_defect_upper) or self.local_defect_upper < 0:
            raise ValueError("local defect must be finite and nonnegative")
        if self.sensitivity_upper is not None:
            if not math.isfinite(self.sensitivity_upper) or self.sensitivity_upper < 0:
                raise ValueError("sensitivity upper bound must be finite and nonnegative")
        if not math.isfinite(self.requested_horizon) or self.requested_horizon <= 0:
            raise ValueError("requested horizon must be finite and positive")


@dataclass(frozen=True)
class HorizonCertificate:
    contract: ResidualHorizonContract
    propagated_upper: float | None
    tolerance: float
    status: HorizonStatus
    reason: str

    @property
    def passed(self) -> bool:
        return self.status is HorizonStatus.HORIZON_CERTIFIED


def certify_horizon(
    contract: ResidualHorizonContract,
    *,
    in_trust_region: bool,
    propagated_upper: float | None,
    tolerance: float,
) -> HorizonCertificate:
    contract.validate()
    if not math.isfinite(tolerance) or tolerance < 0:
        raise ValueError("tolerance must be finite and nonnegative")

    if not in_trust_region:
        return HorizonCertificate(
            contract,
            None,
            tolerance,
            HorizonStatus.OUTSIDE_TRUST_REGION,
            "requested propagation leaves the declared trust region",
        )

    if propagated_upper is None:
        return HorizonCertificate(
            contract,
            None,
            tolerance,
            HorizonStatus.HORIZON_BOUND_UNAVAILABLE,
            "small local residual is not a horizon bound",
        )

    if not math.isfinite(propagated_upper) or propagated_upper < 0:
        raise ValueError("propagated_upper must be finite and nonnegative")

    if propagated_upper <= tolerance:
        return HorizonCertificate(
            contract,
            propagated_upper,
            tolerance,
            HorizonStatus.HORIZON_CERTIFIED,
            "propagated residual is inside the declared tolerance",
        )

    return HorizonCertificate(
        contract,
        propagated_upper,
        tolerance,
        HorizonStatus.HORIZON_UNSAFE,
        "propagated residual exceeds the declared tolerance",
    )
