"""Domain-neutral OoL-MVS 2.7.7 evidence primitives adapted for RHRC.

The scientific 24-claim registry is deliberately not imported. These objects
harden evidence identity, hashing and ancestry for RH research governance only.
"""
from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
from enum import Enum
from typing import Any, Iterable, Mapping
import hashlib
import json
import math


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


def canonical_value(x: Any) -> Any:
    if isinstance(x, Enum):
        return {"$enum": type(x).__module__ + "." + type(x).__qualname__, "value": x.value}
    if x is None or type(x) in (bool, str):
        return x
    if type(x) is int:
        return {"$int": str(x)}
    if type(x) is float:
        if not math.isfinite(x):
            raise ValueError("nonfinite_canonical_number")
        return {"$float": x.hex()}
    if type(x) is bytes:
        return {"$bytes": x.hex()}
    if is_dataclass(x) and not isinstance(x, type):
        return {
            "$record": type(x).__module__ + "." + type(x).__qualname__,
            "fields": {f.name: canonical_value(getattr(x, f.name)) for f in fields(x)},
        }
    if type(x) is tuple:
        return {"$tuple": [canonical_value(v) for v in x]}
    if type(x) is list:
        return {"$list": [canonical_value(v) for v in x]}
    if type(x) is dict:
        if any(type(k) is not str for k in x):
            raise TypeError("canonical_mapping_keys_must_be_strings")
        return {"$map": {k: canonical_value(x[k]) for k in sorted(x)}}
    raise TypeError("unsupported_canonical_type:" + type(x).__name__)


def canonical_bytes(obj: Any) -> bytes:
    return json.dumps(
        canonical_value(obj), ensure_ascii=False, sort_keys=True,
        separators=(",", ":"), allow_nan=False
    ).encode("utf-8")


def stable_digest(obj: Any) -> str:
    return hashlib.sha256(canonical_bytes(obj)).hexdigest()


def bytes_ref(data: bytes) -> str:
    if type(data) is not bytes:
        raise TypeError("raw_object_must_be_bytes")
    return "sha256:" + hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class EvidenceReceipt:
    evidence_id: str
    witness_refs: tuple[str, ...] = ()
    raw_measurement_refs: tuple[str, ...] = ()
    provenance_refs: tuple[str, ...] = ()
    assay_id: str = ""
    observation_window: str = ""
    input_digest: str = ""
    parent_evidence_refs: tuple[str, ...] = ()
    origin: str = "UNCLASSIFIED"


@dataclass(frozen=True)
class DomainReceipt:
    type_id: str
    values: tuple[Any, ...]
    completeness: DomainCompleteness
    enumeration_method: str = ""
    evidence_ref: str = ""
    scope_route_digest: str = ""


@dataclass(frozen=True)
class ClaimResult:
    claim_id: str
    result: EvidenceValue
    support_receipt_digests: tuple[str, ...]
    registry_hash: str
    evaluation_mode: str = "EXPERIMENTAL_EVIDENCE"
    typed_arguments: tuple[Any, ...] = ()
    physical_witness_ref: str = ""
    evidence_state_digest: str = ""
    runtime_digest: str = ""
    evaluation_digest: str = ""


@dataclass(frozen=True)
class ClaimCertificate:
    claim_id: str
    physical_witness_ref: str
    claim_result: EvidenceValue
    certificate_status: CertificateStatus
    registry_hash: str
    reason_codes: tuple[str, ...] = ()
    assurance_scope: str = "NO_ATTESTATION"
    policy_digest: str = ""
    scientific_validation: str = "NOT_ESTABLISHED_BY_SOFTWARE"


def evidence_closure(refs: Iterable[str], env: Mapping[str, EvidenceReceipt]) -> dict[str, EvidenceReceipt]:
    resolved: dict[str, EvidenceReceipt] = {}
    visiting: set[str] = set()

    def walk(eid: str) -> None:
        if eid in visiting:
            raise ValueError("cyclic_evidence_ancestry")
        if eid in resolved:
            return
        rec = env.get(eid)
        if not isinstance(rec, EvidenceReceipt) or rec.evidence_id != eid:
            raise ValueError("missing_or_invalid_raw_evidence:" + str(eid))
        if rec.origin not in {"LABORATORY", "MODEL", "SYNTHETIC", "REPOSITORY"}:
            raise ValueError("unclassified_evidence_origin:" + eid)
        visiting.add(eid)
        for parent in rec.parent_evidence_refs:
            walk(parent)
        visiting.remove(eid)
        resolved[eid] = rec

    for ref in refs:
        walk(ref)
    return resolved
