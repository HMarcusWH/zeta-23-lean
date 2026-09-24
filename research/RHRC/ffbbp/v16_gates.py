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
    decision_sufficiency_pass: bool | None,
    decision_commutation_pass: bool | None,
    stateful_reduction: bool,
    transition_closure_pass: bool | None,
    horizon_bearing: bool,
    horizon_certificate: HorizonCertificate | None,
    witness_bearing: bool,
    witness_pass: bool | None,
) -> AssuranceGateResult:
    """Fail-closed FFBBP v1.6 assurance gate.

    Snapshot decision sufficiency, diagnostic commutation, decision commutation,
    stateful transition closure, horizon propagation, and witness safety are
    separate obligations.  This gate never inherits or extends RUN42C
    qualification.
    """
    blockers: list[str] = []

    if not diagnostic_commutation_pass:
        blockers.append("DIAGNOSTIC_COMMUTATION_FAIL")

    if decision_bearing:
        if decision_sufficiency_pass is not True:
            blockers.append("DECISION_SUFFICIENCY_NOT_ESTABLISHED")
        if decision_commutation_pass is not True:
            blockers.append("DECISION_COMMUTATION_NOT_ESTABLISHED")

    if stateful_reduction and transition_closure_pass is not True:
        blockers.append("STATEFUL_TRANSITION_CLOSURE_NOT_ESTABLISHED")

    if horizon_bearing:
        if horizon_certificate is None:
            blockers.append("HORIZON_CERTIFICATE_MISSING")
        elif horizon_certificate.status is not HorizonStatus.HORIZON_CERTIFIED:
            blockers.append(f"HORIZON_NOT_CERTIFIED:{horizon_certificate.status.value}")

    if witness_bearing and witness_pass is not True:
        blockers.append("WITNESS_NOT_CLAIM_SAFE")

    return AssuranceGateResult(not blockers, tuple(blockers))
