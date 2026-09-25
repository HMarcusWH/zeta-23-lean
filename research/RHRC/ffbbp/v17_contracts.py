from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
import re

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class GateStatus(str, Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    NOT_APPLICABLE = "NOT_APPLICABLE"
    NOT_EVALUATED = "NOT_EVALUATED"


@dataclass(frozen=True)
class QualificationIdentity:
    """FFBBP 1.7 profile/protocol/execution identity.

    A material change at any level is a different qualification object unless a
    separately justified equivalence result is supplied. This record does not
    itself qualify an execution.
    """

    profile_id: str
    profile_digest: str
    protocol_id: str
    protocol_digest: str
    execution_id: str
    execution_digest: str

    def validate(self) -> None:
        for label, value in (
            ("profile_id", self.profile_id),
            ("protocol_id", self.protocol_id),
            ("execution_id", self.execution_id),
        ):
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"{label} must be nonempty")
        for label, value in (
            ("profile_digest", self.profile_digest),
            ("protocol_digest", self.protocol_digest),
            ("execution_digest", self.execution_digest),
        ):
            if not isinstance(value, str) or _SHA256_RE.fullmatch(value) is None:
                raise ValueError(f"{label} must be lowercase sha256")


@dataclass(frozen=True)
class TypedGateResult:
    key: str
    status: GateStatus
    owner: str
    identity: str
    scope: str
    evidence_kind: str
    evidence_ref: str

    def validate(self) -> None:
        if not isinstance(self.status, GateStatus):
            raise ValueError("status must be GateStatus")
        for label, value in (
            ("key", self.key),
            ("owner", self.owner),
            ("identity", self.identity),
            ("scope", self.scope),
            ("evidence_kind", self.evidence_kind),
            ("evidence_ref", self.evidence_ref),
        ):
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"{label} must be nonempty")

    @property
    def satisfied(self) -> bool:
        return self.status is GateStatus.PASS


def required_gate_satisfied(result: TypedGateResult) -> bool:
    """Required FFBBP 1.7 gates are satisfied only by PASS.

    NOT_APPLICABLE is legal only when the frozen protocol omitted/scoped out the
    obligation; it is never converted to PASS here. NOT_EVALUATED is unresolved.
    """
    result.validate()
    return result.status is GateStatus.PASS
