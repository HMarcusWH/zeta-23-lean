"""Fail-closed certificate authority surface adapted from OoL-MVS 2.7.7.

This module authenticates reviewed bindings; it never upgrades them to physical
or mathematical truth. RH theorem authority remains Lean/compiler only.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey

from ool.v277_evidence import ClaimCertificate, ClaimResult, CertificateStatus, EvidenceValue, canonical_bytes, stable_digest
from ool.v277_thresholds import timestamp


@dataclass(frozen=True)
class EvaluatorRegistration:
    evaluator_id: str
    evaluator_version: str
    code_digest: str
    symbols: tuple[str, ...]
    qualification_ref: str


@dataclass(frozen=True)
class VerifierPolicy:
    policy_id: str
    registry_hashes: tuple[str, ...]
    runtime_hashes: tuple[str, ...]
    trusted_keys: tuple[tuple[str, bytes], ...]
    evaluators: tuple[EvaluatorRegistration, ...] = ()
    preregistration_digests: tuple[str, ...] = ()
    frozen_threshold_digests: tuple[str, ...] = ()
    allow_synthetic: bool = False


@dataclass(frozen=True)
class Attestation:
    object_digest: str
    object_kind: str
    issuer_id: str
    signed_at: str
    evaluator_code_digest: str = ""
    qualification_ref: str = ""
    signature: bytes = b""


def attestation_payload(a: Attestation) -> Attestation:
    return replace(a, signature=b"")


def sign_reviewed_object(
    obj: object,
    kind: str,
    issuer_id: str,
    key: Ed25519PrivateKey,
    *,
    signed_at: str,
    evaluator_code_digest: str = "",
    qualification_ref: str = "",
) -> Attestation:
    timestamp(signed_at)
    a = Attestation(stable_digest(obj), kind, issuer_id, signed_at, evaluator_code_digest, qualification_ref)
    return replace(a, signature=key.sign(canonical_bytes(attestation_payload(a))))


def verified_attestation_count(policy: VerifierPolicy, attestations: Iterable[Attestation]) -> int:
    keys = dict(policy.trusted_keys)
    if not keys or len(keys) != len(policy.trusted_keys):
        return 0
    count = 0
    for a in attestations:
        if not isinstance(a, Attestation) or a.issuer_id not in keys:
            continue
        try:
            timestamp(a.signed_at)
            Ed25519PublicKey.from_public_bytes(keys[a.issuer_id]).verify(
                a.signature, canonical_bytes(attestation_payload(a))
            )
        except (ValueError, TypeError, InvalidSignature):
            continue
        count += 1
    return count


def issue_certificate(
    result: ClaimResult,
    *,
    physical_witness_ref: str,
    raw_support_complete: bool,
    binding_valid: bool,
    policy: VerifierPolicy | None = None,
    attestations: Iterable[Attestation] = (),
) -> ClaimCertificate:
    """Domain-neutral RHRC adaptation of the 2.7.7 default-incomplete rule."""
    if not isinstance(result, ClaimResult) or not isinstance(result.result, EvidenceValue):
        raise TypeError("typed_claim_result_required")
    if not binding_valid:
        status = CertificateStatus.INVALID
        reasons = ("binding_invalid",)
        assurance = "NO_ATTESTATION"
    elif result.result is EvidenceValue.NA or not raw_support_complete:
        status = CertificateStatus.INCOMPLETE
        reasons = ("unresolved_or_incomplete_support",)
        assurance = "NO_ATTESTATION"
    elif not isinstance(policy, VerifierPolicy):
        status = CertificateStatus.INCOMPLETE
        reasons = ("trusted_verifier_policy_required",)
        assurance = "NO_ATTESTATION"
    elif result.registry_hash not in policy.registry_hashes or result.runtime_digest not in policy.runtime_hashes:
        status = CertificateStatus.INVALID
        reasons = ("code_or_registry_not_authorized",)
        assurance = "NO_ATTESTATION"
    elif verified_attestation_count(policy, attestations) == 0:
        status = CertificateStatus.INCOMPLETE
        reasons = ("reviewed_attestation_required",)
        assurance = "NO_ATTESTATION"
    else:
        status = CertificateStatus.VALID
        reasons = ("signatures_authenticate_reviewed_binding_not_truth",)
        assurance = "ATTESTED_EVIDENCE_BINDING"
    return ClaimCertificate(
        claim_id=result.claim_id,
        physical_witness_ref=physical_witness_ref,
        claim_result=result.result,
        certificate_status=status,
        registry_hash=result.registry_hash,
        reason_codes=reasons,
        assurance_scope=assurance,
        policy_digest=stable_digest(policy) if policy is not None else "",
    )
