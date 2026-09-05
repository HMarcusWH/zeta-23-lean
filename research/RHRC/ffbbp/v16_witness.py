from __future__ import annotations

from dataclasses import dataclass

from ffbbp.v16_contracts import ExplicitWitnessCertificate, MaskingStatus


@dataclass(frozen=True)
class WitnessGateResult:
    passed: bool
    blockers: tuple[str, ...]


def assess_witness(cert: ExplicitWitnessCertificate) -> WitnessGateResult:
    cert.validate()
    blockers: list[str] = []
    if not cert.visibility_pass:
        blockers.append("WITNESS_VISIBILITY_FAIL")
    if not cert.perturbation_safe:
        blockers.append("WITNESS_MARGIN_NOT_PERTURBATION_SAFE")
    if cert.masking_status is MaskingStatus.UNRESOLVED:
        blockers.append("WITNESS_MASKING_UNRESOLVED")
    elif cert.masking_status is MaskingStatus.FAILED:
        blockers.append("WITNESS_MASKING_FAIL")
    return WitnessGateResult(not blockers, tuple(blockers))
