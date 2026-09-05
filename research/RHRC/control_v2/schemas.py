from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum


class Authority(str, Enum):
    THEOREM = "THEOREM"
    DERIVED = "DERIVED"
    DIAGNOSTIC = "DIAGNOSTIC"
    HEURISTIC = "HEURISTIC"
    HISTORICAL = "HISTORICAL"


class Disposition(str, Enum):
    CONTINUE = "CONTINUE"
    ZOOM = "ZOOM"
    REFINE = "REFINE"
    BRANCH = "BRANCH"
    RELOCK = "RELOCK"
    PRUNE = "PRUNE"
    ABSTAIN = "ABSTAIN"


@dataclass(frozen=True)
class TheoremAnchor:
    pr: int
    merge_commit: str
    tree: str
    status: str


@dataclass(frozen=True)
class ControlAnchor:
    pr: int
    merge_commit: str
    tree: str
    status: str


@dataclass(frozen=True)
class ResidualVector:
    proof: float | None = None
    metric: float | None = None
    normalization: float | None = None
    visibility: float | None = None
    masking: float | None = None
    commutation: float | None = None
    horizon: float | None = None
    resonance: float | None = None
    provenance: float | None = None


@dataclass(frozen=True)
class ResearchState:
    boundary_id: str
    terminal_claim: str
    anchor: TheoremAnchor
    control_anchor: ControlAnchor
    frontier_id: str
    open_obligations: tuple[str, ...]
    residuals: ResidualVector = ResidualVector()


@dataclass(frozen=True)
class ResearchAction:
    action_id: str
    kind: str
    concept_id: str
    cost: float
    information_gain: float
    falsification_value: float
    closure_value: float
    residual_risk: float
    dependency_debt: float
    retro_search_required: bool
    first_break_required: bool
    decision_commutation_required: bool
    horizon_required_for_tail_claim: bool
    dead_route_matches: tuple[str, ...] = ()
    surviving_objections: tuple[str, ...] = ()


@dataclass(frozen=True)
class RouteCertificate:
    frontier_id: str
    selected_action: str | None
    score: float | None
    disposition: Disposition
    rationale: tuple[str, ...]
    retro_receipt_ids: tuple[str, ...]
    surviving_objections: tuple[str, ...]
    required_relock: tuple[str, ...]
    theorem_authority: bool = False
    terminal_claim_change: bool = False

    def to_dict(self) -> dict:
        out = asdict(self)
        out["disposition"] = self.disposition.value
        return out
