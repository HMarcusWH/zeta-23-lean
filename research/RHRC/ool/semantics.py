from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Mapping

from ool.v277_evidence import (
    CertificateStatus,
    ClaimCertificate,
    ClaimResult,
    DomainCompleteness,
    EvidenceReceipt,
    EvidenceValue,
    stable_digest,
)
from ool.v277_authority import Attestation, EvaluatorRegistration, VerifierPolicy, issue_certificate


def k_not(x: EvidenceValue) -> EvidenceValue:
    return {
        EvidenceValue.PASS: EvidenceValue.FAIL,
        EvidenceValue.FAIL: EvidenceValue.PASS,
        EvidenceValue.NA: EvidenceValue.NA,
    }[x]


def k_and(xs: Iterable[EvidenceValue]) -> EvidenceValue:
    vals = tuple(xs)
    if any(x is EvidenceValue.FAIL for x in vals):
        return EvidenceValue.FAIL
    if vals and all(x is EvidenceValue.PASS for x in vals):
        return EvidenceValue.PASS
    return EvidenceValue.NA


def k_or(xs: Iterable[EvidenceValue]) -> EvidenceValue:
    vals = tuple(xs)
    if any(x is EvidenceValue.PASS for x in vals):
        return EvidenceValue.PASS
    if vals and all(x is EvidenceValue.FAIL for x in vals):
        return EvidenceValue.FAIL
    return EvidenceValue.NA


def exists_result(xs: Iterable[EvidenceValue], completeness: DomainCompleteness) -> EvidenceValue:
    vals = tuple(xs)
    if any(x is EvidenceValue.PASS for x in vals):
        return EvidenceValue.PASS
    if completeness is DomainCompleteness.COMPLETE and all(x is EvidenceValue.FAIL for x in vals):
        return EvidenceValue.FAIL
    return EvidenceValue.NA


def forall_result(xs: Iterable[EvidenceValue], completeness: DomainCompleteness) -> EvidenceValue:
    vals = tuple(xs)
    if any(x is EvidenceValue.FAIL for x in vals):
        return EvidenceValue.FAIL
    if completeness is DomainCompleteness.COMPLETE and all(x is EvidenceValue.PASS for x in vals):
        return EvidenceValue.PASS
    return EvidenceValue.NA


@dataclass(frozen=True)
class RouteBinding:
    route_id: str
    boundary_id: str
    boundary_digest: str
    route_spec_digest: str
    phase: str


def confirmatory_binding_status(expected: RouteBinding, observed: RouteBinding) -> str:
    if expected.phase != "CONFIRMATORY_FROZEN":
        return "ROUTE_NOT_FROZEN"
    if observed.route_id != expected.route_id or observed.boundary_id != expected.boundary_id:
        return "STRUCTURAL_BINDING_MISMATCH"
    if observed.boundary_digest != expected.boundary_digest:
        return "NEW_ROUTE_REQUIRED"
    if observed.route_spec_digest != expected.route_spec_digest:
        return "NEW_ROUTE_REQUIRED"
    return "BOUND"


@dataclass(frozen=True)
class LeafEvaluationReceipt:
    predicate_id: str
    evidence_receipt_refs: tuple[str, ...]
    result: EvidenceValue
    authority_mode: str = "AUTHORIZED_EVALUATOR"


def validate_leaf_receipt(
    leaf: LeafEvaluationReceipt,
    raw_evidence: Mapping[str, EvidenceReceipt],
) -> EvidenceValue:
    if leaf.authority_mode != "AUTHORIZED_EVALUATOR":
        return EvidenceValue.NA
    if not leaf.evidence_receipt_refs:
        return EvidenceValue.NA
    if any(ref not in raw_evidence for ref in leaf.evidence_receipt_refs):
        return EvidenceValue.NA
    return leaf.result


def unconditional_provenance_result(
    required_nodes: Iterable[str],
    provenance: Mapping[str, str],
    *,
    complete: bool,
) -> EvidenceValue:
    allowed = {"ADMITTED_UNCONDITIONAL_ROOT", "DESCENDANT_OF_ADMITTED_UNCONDITIONAL_ROOT"}
    unresolved = False
    for node in required_nodes:
        state = provenance.get(node, "UNKNOWN")
        if state in {"CONDITIONAL", "CONJECTURAL", "EXTERNAL_NONADMITTED"}:
            return EvidenceValue.FAIL
        if state not in allowed:
            unresolved = True
    if unresolved or not complete:
        return EvidenceValue.NA
    return EvidenceValue.PASS


def absence_result(*, forbidden_observed: bool, search_domain_complete: bool) -> EvidenceValue:
    if forbidden_observed:
        return EvidenceValue.FAIL
    if not search_domain_complete:
        return EvidenceValue.NA
    return EvidenceValue.PASS


@dataclass(frozen=True)
class RouteInterfaceQualification:
    interface_id: str
    result: EvidenceValue
    actual_output_bound: bool
    provenance_continuous: bool


def integrated_route_freeze_status(
    interfaces: Iterable[RouteInterfaceQualification],
) -> str:
    vals = tuple(interfaces)
    if not vals:
        return "INCOMPLETE"
    if any(x.result is EvidenceValue.FAIL for x in vals):
        return "QUALIFICATION_FAILED"
    if any(x.result is EvidenceValue.NA for x in vals):
        return "NOT_READY_FOR_FREEZE"
    if any(not x.actual_output_bound for x in vals):
        return "NOT_READY_FOR_FREEZE"
    if any(not x.provenance_continuous for x in vals):
        return "NOT_READY_FOR_FREEZE"
    return "FULL_ROUTE_FREEZE_ELIGIBLE"


__all__ = [
    "Attestation",
    "CertificateStatus",
    "ClaimCertificate",
    "ClaimResult",
    "DomainCompleteness",
    "EvidenceReceipt",
    "EvidenceValue",
    "EvaluatorRegistration",
    "LeafEvaluationReceipt",
    "RouteBinding",
    "RouteInterfaceQualification",
    "VerifierPolicy",
    "absence_result",
    "confirmatory_binding_status",
    "exists_result",
    "forall_result",
    "integrated_route_freeze_status",
    "issue_certificate",
    "k_and",
    "k_not",
    "k_or",
    "stable_digest",
    "unconditional_provenance_result",
    "validate_leaf_receipt",
]
