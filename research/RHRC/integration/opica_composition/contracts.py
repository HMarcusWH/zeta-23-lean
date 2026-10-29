"""Closed, serializable evaluator records, separate from Lean Expr encoding.

These records identify inputs; constructing one never authenticates evidence.
Only an independent native replay may produce publication-eligible evidence.
"""
from __future__ import annotations
from dataclasses import dataclass, fields, asdict
from pathlib import Path
from typing import Any, ClassVar
from .canonical import require, closed_keys, digest, digest_text, nonempty_text, canonical_bytes, load_bytes, validate_path_inventory, native_evidence_bytes, load_native_evidence, NATIVE_EVIDENCE_CODEC
import re
import hashlib

STATUSES = frozenset({"PROVED_CONDITIONAL", "TYPE_REJECTED_THIS_APPLICATION", "ADAPTER_REQUIRED",
    "UNRESOLVED", "NO_MATCH_IN_GRAMMAR", "RESOURCE_EXHAUSTED", "ENVIRONMENT_ERROR"})

BASELINE_INPUT_LANES=("CONTRACT","PARENT_REGRESSION","CURRENT_COMPATIBILITY","COMPOSITION_FORMAL","SEMANTIC_NEGATIVES",
       "FRAMEWORK_ADAPTERS","PROVIDER_SELECTED","REPLAY_CAMPAIGN","GENERATED_STATE")
BASELINE_LANES=BASELINE_INPUT_LANES+("ACCEPTANCE",)
ROUND4_LANES=BASELINE_INPUT_LANES+("MATHEMATICAL_SUPPORT","SOURCE_NUMERICS")
LANES=ROUND4_LANES+("ACCEPTANCE",)
PER_ATTEMPT_GATES=["SOURCE","KERNEL","AXIOMS","INDEPENDENT_EXPECTED_TYPE"]

def validate_lane_id(value):
    require(type(value)is str and value in LANES,"unknown canonical lane ID")
    return value

@dataclass(frozen=True)
class Record:
    schema: ClassVar[str] = "OPICA_RECORD_V1"
    json_codec: ClassVar[str | None] = None

    def _bytes(self,value): return native_evidence_bytes(value) if self.json_codec else canonical_bytes(value)
    def _load(self,value): return load_native_evidence(value) if self.json_codec else load_bytes(value)

    def __post_init__(self):
        for f in fields(self):
            value=getattr(self,f.name)
            if f.name.endswith(("_digest","_sha256","_hash")) or f.name in {"generation","source_generation"}:
                digest_text(value,f.name)
            if f.name in {"commit","tree","approved_commit"}:
                require(type(value)is str and re.fullmatch(r"[0-9a-f]{40}",value)is not None,"exact Git object ID required")
            if isinstance(value,(dict,list)):
                # Detach nested caller-owned objects before an attempt starts.
                object.__setattr__(self,f.name,self._load(self._bytes(value)))
        if hasattr(self,"allowed_constants"):
            require(type(self.allowed_constants)is dict,"constant table required")
            for key,value in self.allowed_constants.items(): digest_text(key); nonempty_text(value,"declaration")
        if hasattr(self,"files"):
            validate_path_inventory(self.files)
            for value in self.files.values(): digest_text(value)
        if hasattr(self,"manifest"):
            validate_path_inventory(self.manifest)
            for value in self.manifest.values(): digest_text(value)
        object.__setattr__(self,"_sealed_bytes",self._bytes(self.to_dict()))

    def to_dict(self) -> dict[str, Any]:
        def convert(x):
            if isinstance(x, Path): return str(x)
            if isinstance(x, tuple): return [convert(v) for v in x]
            if isinstance(x, dict): return {k: convert(v) for k, v in x.items()}
            if isinstance(x, list): return [convert(v) for v in x]
            return x
        return {"schema": self.schema, **({"envelope_codec":self.json_codec} if self.json_codec else {}), **convert(asdict(self))}

    def to_bytes(self): return self._bytes(self.to_dict())

    @classmethod
    def from_bytes(cls,raw):
        return cls.from_dict(load_native_evidence(raw) if cls.json_codec else load_bytes(raw))

    @classmethod
    def from_dict(cls, value):
        closed_keys(value, {"schema", *(f.name for f in fields(cls)), *({"envelope_codec"} if cls.json_codec else set())})
        require(value["schema"] == cls.schema, "record schema differs")
        if cls.json_codec: require(value["envelope_codec"]==cls.json_codec,"native envelope codec differs")
        return cls(**{f.name: value[f.name] for f in fields(cls)})

    @property
    def digest(self):
        raw=self._bytes(self.to_dict())
        require(raw==self._sealed_bytes,"record mutated after freezing")
        return hashlib.sha256(self.schema.encode("utf-8")+b"\0"+raw).hexdigest()

@dataclass(frozen=True)
class ExperimentSpec(Record):
    schema: ClassVar[str] = "OPICA_EXPERIMENT_SPEC_V1"
    profile_id: str
    approved_commit: str
    source_files: dict[str, str]
    environment: dict[str, Any]
    source_policy: str = "DRAFT"

@dataclass(frozen=True)
class SnapshotIdentity(Record):
    schema: ClassVar[str] = "OPICA_SOURCE_SNAPSHOT_V1"
    repo: str
    commit: str
    tree: str
    source_digest: str
    generation: str
    files: dict[str, str]
    environment: dict[str, Any]
    profile_id: str
    source_policy: str = "DRAFT"

    def __post_init__(self):
        require(type(self.files)is dict and bool(self.files) and type(self.environment)is dict,"complete source/environment inventory required")
        require(self.source_policy in {"DRAFT","REVIEWED_FROZEN"},"source policy differs")
        super().__post_init__()

@dataclass(frozen=True)
class StatementContract(Record):
    schema: ClassVar[str] = "OPICA_STATEMENT_CONTRACT_V1"
    declaration: str
    module: str
    type_expression: dict[str, Any]
    type_sha256: str
    universe_parameters: list[str]
    outer_telescope: list[dict[str, Any]]
    conclusion_text: str
    type_constants: list[str]
    value_constants: list[str]
    axioms: list[str]

    def __post_init__(self):
        from .inventory import expression_hash,validate_telescope
        for value in (self.declaration,self.module,self.conclusion_text):nonempty_text(value,'statement identity')
        require(expression_hash(self.type_expression)==self.type_sha256,"statement expression hash differs")
        validate_telescope(self.type_expression,self.outer_telescope)
        for values in (self.universe_parameters,self.type_constants,self.value_constants,self.axioms):
            require(type(values)is list and all(type(x)is str for x in values) and len(values)==len(set(values)),"closed statement name inventory required")
        super().__post_init__()

@dataclass(frozen=True)
class StatementInventory(Record):
    schema: ClassVar[str] = "OPICA_STATEMENT_INVENTORY_V1"
    json_codec: ClassVar[str] = NATIVE_EVIDENCE_CODEC
    snapshot_digest: str
    statements: list[dict[str, Any]]
    native_export_sha256: str

@dataclass(frozen=True)
class CohortInventory(Record):
    schema: ClassVar[str] = "OPICA_COHORT_INVENTORY_V1"
    declarations: list[str]
    memberships: list[dict[str, str]] = None

@dataclass(frozen=True)
class CoverageReport(Record):
    schema: ClassVar[str] = "OPICA_COVERAGE_REPORT_V1"
    complete: bool
    missing: list[str]
    unexpected: list[str]
    duplicates: list[str]

@dataclass(frozen=True)
class TargetSpec(Record):
    schema: ClassVar[str] = "OPICA_TARGET_SPEC_V1"
    target_id: str
    declaration: str
    module: str
    expected_type_hash: str
    allowed_constants: dict[str, str]
    allowed_axioms: list[str]
    imports: list[str]
    required_gates: list[str]
    target_kind: str = "value"
    forbidden_constants: list[str] = None

    def __post_init__(self):
        require(type(self.required_gates)is list and self.required_gates==PER_ATTEMPT_GATES,"exact supported per-attempt gate inventory required")
        require(type(self.allowed_axioms)is list and all(type(x)is str for x in self.allowed_axioms),"axiom name list required")
        require(type(self.imports)is list and self.module in self.imports,"exact evaluator target import required")
        require(self.target_kind in {"value","type"},"target kind differs")
        super().__post_init__()

@dataclass(frozen=True)
class GrammarProfile(Record):
    schema: ClassVar[str] = "OPICA_GRAMMAR_PROFILE_V1"
    excluded_declarations: list[str]
    approved_adapters: list[str]

@dataclass(frozen=True)
class SearchBudget(Record):
    schema: ClassVar[str] = "OPICA_SEARCH_BUDGET_V2"
    candidates: int = 128
    term_nodes: int = 2048
    term_depth: int = 64
    heartbeats: int = 800000
    wall_seconds: int = 600
    output_bytes: int = 8388608
    memory_bytes: int = 4294967296
    disk_bytes: int = 4294967296
    cpu_seconds: int | None = None
    max_file_bytes: int | None = None

    def __post_init__(self):
        # Resolve omitted fields to the old recipe's effective limits. Existing
        # short wall/log configurations must not silently gain CPU/file space.
        if self.cpu_seconds is None and type(self.wall_seconds)is int:
            object.__setattr__(self,"cpu_seconds",min(self.wall_seconds,600))
        if self.max_file_bytes is None and type(self.output_bytes)is int:
            object.__setattr__(self,"max_file_bytes",min(self.output_bytes,8388608))
        require(all(type(v) is int and v > 0 for v in asdict(self).values()), "positive finite resource caps required")
        require(self.term_depth <= 64 and self.term_nodes <= 100000 and self.candidates <= 10000,
                "grammar resource hard cap exceeded")
        require(self.cpu_seconds<=min(self.wall_seconds,600) and self.max_file_bytes<=8388608,
                "worker CPU/file hard cap exceeded")
        super().__post_init__()

    @property
    def log_bytes(self):
        """Explicit log limit; output_bytes remains the compatible wire name."""
        return self.output_bytes

@dataclass(frozen=True)
class CompositionProposal(Record):
    schema: ClassVar[str] = "OPICA_COMPOSITION_PROPOSAL_RECORD_V1"
    proposal_id: str
    target_id: str
    source_generation: str
    plan: dict[str, Any]

@dataclass(frozen=True)
class CandidateBatch(Record):
    schema: ClassVar[str] = "OPICA_CANDIDATE_BATCH_V1"
    inventory_digest: str
    target_id: str
    candidates: list[dict[str, Any]]
    complete: bool
    disposition: str

@dataclass(frozen=True)
class AttemptArtifacts(Record):
    schema: ClassVar[str] = "OPICA_ATTEMPT_ARTIFACTS_V1"
    status: str
    target_digest: str
    snapshot_digest: str
    proposal_digest: str
    output: str
    manifest: dict[str, str]
    native: dict[str, Any]
    reason: str = ""

    def __post_init__(self):
        require(self.status in STATUSES, "unknown attempt status")
        super().__post_init__()

@dataclass(frozen=True)
class VerifiedApplication(Record):
    schema: ClassVar[str] = "OPICA_VERIFIED_APPLICATION_V1"
    status: str
    target_digest: str
    snapshot_digest: str
    proposal_digest: str
    evidence_digest: str
    source_generation: str
    axioms: list[str]
    constants: list[str]
    context: list[dict[str, Any]]
    independent_replay: dict[str, Any]
    publication_eligible: bool = False
    object_bindings: list[dict[str, Any]] = None

    def __post_init__(self):
        require(self.status in STATUSES, "unknown verification status")
        require(type(self.publication_eligible)is bool,"publication flag must be boolean")
        super().__post_init__()

@dataclass(frozen=True)
class WorkerConfig(Record):
    """Trusted host configuration; never parsed from a proposal."""
    schema: ClassVar[str] = "OPICA_WORKER_CONFIG_V1"
    lean: str
    toolchain_root: str
    lean_paths: list[str]
    bubblewrap: str = "/usr/bin/bwrap"
    prlimit: str = "/usr/bin/prlimit"
    production: bool = True
    budget: dict[str, int] = None

    def __post_init__(self):
        require(type(self.production)is bool,"worker production mode must be boolean")
        require(type(self.lean_paths)is list and bool(self.lean_paths) and all(type(p)is str for p in self.lean_paths),"closed import path inventory required")
        if self.budget is not None: SearchBudget(**self.budget)
        super().__post_init__()

@dataclass(frozen=True)
class ObjectBinding(Record):
    schema: ClassVar[str] = "OPICA_OBJECT_BINDING_V1"
    source_digest: str
    context_digest: str
    scope_index: int
    object_kind: str
    term_expression: dict[str, Any]
    type_expression: dict[str, Any]
    context: list[dict[str, Any]]
    physical_source: dict[str, Any] | None = None
    aperture: dict[str, Any] | None = None
    cutoff: dict[str, Any] | None = None
    parity: dict[str, Any] | None = None
    normalization: dict[str, Any] | None = None
    residual_contract: dict[str, Any] | None = None

    def __post_init__(self):
        require(type(self.scope_index)is int and self.scope_index>=0,"ordered object scope required")
        require(self.object_kind in {"AUTHORIZED_LOCAL","DEPENDENT_PROOF_PACKET","CHECKED_VIEW"},"object kind differs")
        from .inventory import expression_hash
        expression_hash(self.term_expression); expression_hash(self.type_expression)
        # Optional physical fields are actual closed expressions, never labels
        # claiming two independently chosen same-type values are identical.
        for field in (self.physical_source,self.aperture,self.cutoff,self.parity,self.normalization,self.residual_contract):
            if field is not None: expression_hash(field)
        super().__post_init__()

@dataclass(frozen=True)
class AdapterObligation(Record):
    schema: ClassVar[str] = "OPICA_ADAPTER_OBLIGATION_V1"
    obligation_id: str
    source_generation: str
    target_digest: str
    context_digest: str
    expected_expression: dict[str, Any]
    context: list[dict[str, Any]]
    disposition: str = "OPEN"

    def __post_init__(self):
        require(self.disposition in {"OPEN","ADAPTER_REQUIRED","UNRESOLVED"},"obligation cannot assert proof")
        from .inventory import expression_hash
        expression_hash(self.expected_expression)
        super().__post_init__()

@dataclass(frozen=True)
class RouteSpec(Record):
    schema: ClassVar[str] = "OPICA_ROUTE_SPEC_RECORD_V1"
    route_id: str
    source_generation: str
    phase: str
    target_digest: str
    context_digest: str
    authorized_premise_refs: list[str]
    interfaces: list[dict[str, Any]]
    required_gates: list[str]

    def __post_init__(self):
        require(self.phase in {"DISCOVERY","CONFIRMATORY_FROZEN"},"route phase differs")
        require(type(self.required_gates)is list and bool(self.required_gates),"verification gate inventory required")
        for ref in self.authorized_premise_refs: digest_text(ref)
        for row in self.interfaces:
            closed_keys(row,{"interface_id","producer","consumer","transport_ref"})
            for name in ("producer","consumer"): ObjectBinding.from_dict(row[name])
            if row["transport_ref"] is not None: digest_text(row["transport_ref"])
        super().__post_init__()

@dataclass(frozen=True)
class ApplicationReceipt(Record):
    schema: ClassVar[str] = "OPICA_APPLICATION_RECEIPT_RECORD_V1"
    attempt_id: str
    source_generation: str
    target_digest: str
    context_digest: str
    result: str
    used_authorized_premise_refs: list[str]
    remaining_obligation_refs: list[str]
    raw_artifacts: dict[str, str]
    axioms: list[str]
    actual_type_expression: dict[str, Any] | None
    proof_expression: dict[str, Any] | None
    producer_protocol_complete: bool
    object_bindings: list[dict[str, Any]]
    authority: str = "INDEPENDENT_REPLAY_REQUIRED"

    def __post_init__(self):
        require(self.result in STATUSES and type(self.producer_protocol_complete)is bool,"closed receipt disposition required")
        require(self.authority=="INDEPENDENT_REPLAY_REQUIRED","producer cannot grant theorem authority")
        for ref in [*self.used_authorized_premise_refs,*self.remaining_obligation_refs]: digest_text(ref)
        validate_path_inventory(self.raw_artifacts)
        for ref in self.raw_artifacts.values(): digest_text(ref)
        from .inventory import expression_hash
        for expr in (self.actual_type_expression,self.proof_expression):
            if expr is not None: expression_hash(expr)
        for obj in self.object_bindings: ObjectBinding.from_dict(obj)
        super().__post_init__()

def as_record(value, cls):
    return value if type(value) is cls else cls.from_dict(value)
