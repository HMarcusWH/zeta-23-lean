from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum


class CandidateResolutionStatus(str, Enum):
    RESOLVED_UNIQUE = "RESOLVED_UNIQUE"
    RESOLVED_PRIVATE_OR_INTERNAL = "RESOLVED_PRIVATE_OR_INTERNAL"
    NO_COMPILER_MATCH = "NO_COMPILER_MATCH"
    AMBIGUOUS_COMPILER_MATCH = "AMBIGUOUS_COMPILER_MATCH"
    KIND_MISMATCH = "KIND_MISMATCH"


class CandidateVisibility(str, Enum):
    ALREADY_REGISTERED_ROOT = "ALREADY_REGISTERED_ROOT"
    ALREADY_IN_REGISTERED_DEPENDENCY_CLOSURE = "ALREADY_IN_REGISTERED_DEPENDENCY_CLOSURE"
    SOURCE_ONLY_PUBLIC_THEOREM = "SOURCE_ONLY_PUBLIC_THEOREM"
    PRIVATE_OR_INTERNAL_SOURCE_OBJECT = "PRIVATE_OR_INTERNAL_SOURCE_OBJECT"
    AMBIGUOUS_SOURCE_IDENTITY = "AMBIGUOUS_SOURCE_IDENTITY"
    UNRESOLVED_SOURCE_IDENTITY = "UNRESOLVED_SOURCE_IDENTITY"
    KIND_MISMATCH = "KIND_MISMATCH"


@dataclass(frozen=True)
class RepositoryAnchor:
    pr: int
    merge_commit: str
    tree: str
    status: str


@dataclass(frozen=True)
class LeanCandidateReceipt:
    schema_version: str
    repository_graph_authority: RepositoryAnchor
    source_surface_sha256: str
    registered_compiler_receipt_sha256: str
    lean_toolchain: str
    source_declaration_id: str
    path: str
    line: int
    module: str
    declared_name: str
    source_command_kind: str
    trust_zone: str
    resolution_status: str
    visibility_class: str
    resolved_full_name: str | None
    compiler_kind: str | None
    private_or_internal: bool | None
    compiler_type_text: str | None
    compiler_type_sha256: str | None
    registered_claim_id: str | None
    claim_cap: str = "DISCOVERY_ONLY"
    terminal_claim: str = "RH_OPEN"
    theorem_promotion: bool = False

    def to_dict(self) -> dict:
        return asdict(self)
