"""Fail-closed certificate authority surface adapted from OoL-MVS 2.7.7.

This module authenticates reviewed bindings; it never upgrades them to physical
or mathematical truth. RH theorem authority remains Lean/compiler only.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable

from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey

from ool.v277_evidence import (
    ClaimCertificate,
    ClaimResult,
    CertificateStatus,
    EvidenceValue,
    canonical_bytes,
    stable_digest,
)
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
    """Invoke only after human/scientific review; signing does not perform review."""
    timestamp(signed_at)
    a = Attestation(
        stable_digest(obj), kind, issuer_id, signed_at,
        evaluator_code_digest, qualification_ref
    )
    return replace(a, signature=key.sign(canonical_bytes(attestation_payload(a))))


def _verified_attestations(
    policy: VerifierPolicy,
    attestations: Iterable[Attestation],
) -> tuple[dict[tuple[str, str], tuple[Attestation, ...]], str | None]:
    keys = dict(policy.trusted_keys)
    if len(keys) != len(policy.trusted_keys) or not keys:
        return {}, "invalid_trusted_key_configuration"
    grouped: dict[tuple[str, str], list[Attestation]] = {}
    for a in attestations:
        if not isinstance(a, Attestation):
            return {}, "typed_attestation_required"
        if a.issuer_id not in keys:
            continue
        try:
            timestamp(a.signed_at)
            Ed25519PublicKey.from_public_bytes(keys[a.issuer_id]).verify(
                a.signature, canonical_bytes(attestation_payload(a))
            )
        except (ValueError, TypeError, InvalidSignature):
            return {}, "invalid_attestation_signature"
        grouped.setdefault((a.object_kind, a.object_digest), []).append(a)
    return {k: tuple(v) for k, v in grouped.items()}, None


def issue_certificate(
    result: ClaimResult,
    *,
    physical_witness_ref: str,
    raw_support_complete: bool,
    binding_valid: bool,
    policy: VerifierPolicy | None = None,
    attestations: Iterable[Attestation] = (),
) -> ClaimCertificate:
    """RHRC's bounded 2.7.7 authority adapter.

    This deliberately does not import the OoL physical claim registry. Therefore
    VALID means only that this exact RHRC ClaimResult has an authorized reviewed
    signature under an allowed runtime/registry pair. It is not a theorem proof,
    physical truth claim, or scientific qualification.
    """
    if not isinstance(result, ClaimResult) or not isinstance(result.result, EvidenceValue):
        raise TypeError("typed_claim_result_required")

    def finish(status: CertificateStatus, reasons: tuple[str, ...], assurance: str = "NO_ATTESTATION"):
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

    if result.evaluation_mode != "EXPERIMENTAL_EVIDENCE":
        return finish(CertificateStatus.INVALID, ("certificate_requires_experimental_evidence_mode",))
    if result.physical_witness_ref and result.physical_witness_ref != physical_witness_ref:
        return finish(CertificateStatus.INVALID, ("physical_witness_binding_mismatch",))
    if not binding_valid:
        return finish(CertificateStatus.INVALID, ("binding_invalid",))
    if result.result is EvidenceValue.NA or not raw_support_complete:
        return finish(CertificateStatus.INCOMPLETE, ("unresolved_or_incomplete_support",))
    if not isinstance(policy, VerifierPolicy):
        return finish(CertificateStatus.INCOMPLETE, ("trusted_verifier_policy_required",))
    if type(policy.allow_synthetic) is not bool:
        return finish(CertificateStatus.INVALID, ("typed_policy_flag_required",))
    if result.registry_hash not in policy.registry_hashes or result.runtime_digest not in policy.runtime_hashes:
        return finish(CertificateStatus.INVALID, ("code_or_registry_not_authorized",))

    attested, error = _verified_attestations(policy, attestations)
    if error is not None:
        return finish(CertificateStatus.INVALID, (error,))

    required = ("CLAIM_RESULT", stable_digest(result))
    if required not in attested:
        return finish(
            CertificateStatus.INCOMPLETE,
            ("reviewed_attestation_for_exact_claim_result_required",),
        )

    return finish(
        CertificateStatus.VALID,
        ("signatures_authenticate_reviewed_binding_not_physical_truth",),
        "ATTESTED_EVIDENCE_BINDING",
    )
