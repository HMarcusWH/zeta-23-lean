from __future__ import annotations

from dataclasses import dataclass

from ffbbp.v16_horizon import HorizonCertificate, HorizonStatus


@dataclass(frozen=True)
class AssuranceGateResult:
    passed: bool
    blockers: tuple[str, ...]


def reduction_assurance_gate(
    *,
    diagnostic_commutation_pass: bool,
    decision_bearing: bool,
    decision_commutation_pass: bool | None,
    horizon_bearing: bool,
    horizon_certificate: HorizonCertificate | None,
    witness_bearing: bool,
    witness_pass: bool | None,
) -> AssuranceGateResult:
    """Fail-closed v1.6 assurance gate.

    This gate does not inherit or extend RUN42C qualification.  It only checks
    whether a reduced diagnostic has enough assurance to support the declared
    downstream decision/horizon/witness use.
    """
    blockers: list[str] = []

    if not diagnostic_commutation_pass:
        blockers.append("DIAGNOSTIC_COMMUTATION_FAIL")

    if decision_bearing:
        if decision_commutation_pass is not True:
            blockers.append("DECISION_COMMUTATION_NOT_ESTABLISHED")

    if horizon_bearing:
        if horizon_certificate is None:
            blockers.append("HORIZON_CERTIFICATE_MISSING")
        elif horizon_certificate.status is not HorizonStatus.HORIZON_CERTIFIED:
            blockers.append(f"HORIZON_NOT_CERTIFIED:{horizon_certificate.status.value}")

    if witness_bearing and witness_pass is not True:
        blockers.append("WITNESS_NOT_CLAIM_SAFE")

    return AssuranceGateResult(not blockers, tuple(blockers))
