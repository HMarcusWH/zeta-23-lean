from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from math import isfinite
from typing import Optional
import re


@dataclass(frozen=True)
class ThresholdReceipt:
    contract_id: str
    value: float
    preregistered: bool = True
    resolution_relevance_justified: bool = True
    metric: str = "dimensionless"
    units: str = "1"
    d_max: Optional[float] = None
    receipt_id: str = ""
    preregistration_digest: str = ""
    frozen_at: str = ""
    observation_start: str = ""
    applicability: str = ""
    justification: str = ""


def timestamp(x: str) -> datetime:
    if type(x) is not str or not x:
        raise ValueError("timestamp_required")
    d = datetime.fromisoformat(x.replace("Z", "+00:00"))
    if d.tzinfo is None or d.utcoffset() is None:
        raise ValueError("timezone_required")
    return d


def validate_freeze(receipt: ThresholdReceipt) -> tuple[bool, str]:
    if not isinstance(receipt, ThresholdReceipt):
        return False, "typed_threshold_receipt_required"
    if type(receipt.value) not in (int, float) or not isfinite(float(receipt.value)):
        return False, "non_finite_or_non_numeric_value"
    if not receipt.preregistered:
        return False, "not_preregistered"
    if not receipt.resolution_relevance_justified:
        return False, "resolution_or_relevance_not_justified"
    if not re.fullmatch(r"[0-9a-f]{64}", receipt.preregistration_digest):
        return False, "preregistration_digest_required"
    if not receipt.receipt_id or not receipt.applicability.strip() or not receipt.justification.strip():
        return False, "threshold_applicability_justification_required"
    try:
        if timestamp(receipt.frozen_at) >= timestamp(receipt.observation_start):
            return False, "threshold_not_frozen_before_observation"
    except (ValueError, TypeError):
        return False, "invalid_threshold_timestamp"
    return True, "ok"
