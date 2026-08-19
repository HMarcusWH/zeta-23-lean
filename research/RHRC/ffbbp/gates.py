from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

@dataclass(frozen=True)
class GateResult:
    passed: bool
    blockers: tuple[str, ...]


def unknown_field_admission_gate(*, known_null_pass: bool, known_positive_pass: bool,
                                 matched_artifact_pass: bool, firewall_pass: bool,
                                 profile_frozen: bool, domain_adapter_frozen: bool) -> GateResult:
    """FFBBP v1.5 unknown-field diagnostic admission.

    Admission is two-sided and precedes any unknown-field interrogation. Passing this gate
    authorizes diagnostic use only; it does not authorize candidate collapse, domain validation,
    RH evidence, or theorem promotion.
    """
    blockers: list[str] = []
    if not known_null_pass:
        blockers.append("V06N_KNOWN_NULL_FAIL")
    if not known_positive_pass:
        blockers.append("V06P_KNOWN_POSITIVE_FAIL")
    if not matched_artifact_pass:
        blockers.append("V06X_MATCHED_ARTIFACT_FAIL")
    if not firewall_pass:
        blockers.append("SOURCE_TARGET_FIREWALL_FAIL")
    if not profile_frozen:
        blockers.append("PROFILE_NOT_FROZEN")
    if not domain_adapter_frozen:
        blockers.append("DOMAIN_ADAPTER_NOT_FROZEN")
    return GateResult(not blockers, tuple(blockers))


def collapse_gate(*, candidate_rmse: float, null_rmses: Mapping[str, float],
                  known_null_pass: bool, firewall_pass: bool,
                  ablation_pass: bool, transfer_pass: bool,
                  commutation_pass: bool) -> GateResult:
    """Candidate-level fail-closed gate after profile admission.

    This is not the v1.5 unknown-field admission gate. A caller must separately establish
    qualification/admission before interpreting an unknown-domain candidate.
    """
    blockers: list[str] = []
    if not null_rmses:
        blockers.append("NO_LEGAL_NULLS")
    elif candidate_rmse >= min(null_rmses.values()):
        blockers.append("BEST_NULL_NOT_BEATEN")
    if not known_null_pass:
        blockers.append("KNOWN_NULL_FAIL")
    if not firewall_pass:
        blockers.append("SOURCE_TARGET_FIREWALL_FAIL")
    if not ablation_pass:
        blockers.append("CANDIDATE_ALIGNED_ABLATION_FAIL")
    if not transfer_pass:
        blockers.append("TRANSFER_FAIL")
    if not commutation_pass:
        blockers.append("COMMUTATION_FAIL")
    return GateResult(not blockers, tuple(blockers))
