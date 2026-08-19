from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from hashlib import sha256
import json
from typing import Iterable, Mapping


class EvidenceValue(str, Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    NA = "NA"


class CertificateStatus(str, Enum):
    VALID = "VALID"
    INCOMPLETE = "INCOMPLETE"
    INVALID = "INVALID"


class DomainCompleteness(str, Enum):
    COMPLETE = "COMPLETE"
    PARTIAL = "PARTIAL"
    UNKNOWN = "UNKNOWN"


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


def stable_digest(obj: object) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str).encode()
    return sha256(payload).hexdigest()


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
class EvidenceReceipt:
    evidence_id: str
    input_digest: str


@dataclass(frozen=True)
class LeafEvaluationReceipt:
    predicate_id: str
    evidence_receipt_refs: tuple[str, ...]
    result: EvidenceValue
    authority_mode: str = "AUTHORIZED_EVALUATOR"


@dataclass(frozen=True)
class ClaimResult:
    claim_id: str
    result: EvidenceValue
    support_receipt_digests: tuple[str, ...]
    registry_hash: str
    evaluation_mode: str = "EXPERIMENTAL_EVIDENCE"


@dataclass(frozen=True)
class ClaimCertificate:
    claim_id: str
    physical_witness_ref: str
    claim_result: EvidenceValue
    certificate_status: CertificateStatus
    registry_hash: str


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


def issue_certificate(
    result: ClaimResult,
    *,
    physical_witness_ref: str,
    raw_support_complete: bool,
    binding_valid: bool,
) -> ClaimCertificate:
    if not binding_valid:
        status = CertificateStatus.INVALID
    elif result.result is EvidenceValue.NA or not raw_support_complete:
        status = CertificateStatus.INCOMPLETE
    else:
        status = CertificateStatus.VALID
    return ClaimCertificate(
        claim_id=result.claim_id,
        physical_witness_ref=physical_witness_ref,
        claim_result=result.result,
        certificate_status=status,
        registry_hash=result.registry_hash,
    )


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
