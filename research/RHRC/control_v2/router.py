from __future__ import annotations

import json
from pathlib import Path

from control_v2.schemas import Disposition, ResearchAction, ResearchState, RouteCertificate

RHRC = Path(__file__).resolve().parents[1]


def load_actions(path: Path | None = None) -> tuple[ResearchAction, ...]:
    if path is None:
        path = RHRC / "control_v2" / "ACTION_REGISTRY.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    actions: list[ResearchAction] = []
    for action_id, raw in data["actions"].items():
        score = raw["score_inputs"]
        actions.append(ResearchAction(
            action_id=action_id,
            kind=raw["kind"],
            concept_id=raw["concept_id"],
            cost=float(score["cost"]),
            information_gain=float(score["information_gain"]),
            falsification_value=float(score["falsification_value"]),
            closure_value=float(score["closure_value"]),
            residual_risk=float(score["residual_risk"]),
            dependency_debt=float(score["dependency_debt"]),
            retro_search_required=bool(raw.get("retro_search_required", False)),
            first_break_required=bool(raw.get("first_break_required", False)),
            decision_commutation_required=bool(raw.get("decision_commutation_required", False)),
            horizon_required_for_tail_claim=bool(raw.get("horizon_required_for_tail_claim", False)),
            dead_route_matches=tuple(raw.get("dead_route_matches", [])),
            surviving_objections=tuple(raw.get("surviving_objections", [])),
        ))
    return tuple(actions)


def action_score(action: ResearchAction) -> float:
    return (
        action.information_gain
        + action.falsification_value
        + action.closure_value
        - action.cost
        - action.residual_risk
        - action.dependency_debt
    )


def _admissibility_blockers(action: ResearchAction, *, retro_receipt_id: str | None,
                            retro_search_complete: bool | None,
                            first_break_count: int, revival_ids: set[str]) -> tuple[str, ...]:
    blockers: list[str] = []
    if action.retro_search_required and not retro_receipt_id:
        blockers.append("RETRO_SEARCH_RECEIPT_MISSING")
    if action.retro_search_required and retro_search_complete is not True:
        blockers.append("RETRO_SEARCH_INCOMPLETE")
    if action.first_break_required and first_break_count <= 0:
        blockers.append("FIRST_BREAK_CONTRACT_MISSING")
    uncovered_dead = set(action.dead_route_matches) - revival_ids
    if uncovered_dead:
        blockers.append("DEAD_ROUTE_REVIVAL_RECORD_MISSING:" + ",".join(sorted(uncovered_dead)))
    return tuple(blockers)


def recommend(state: ResearchState, actions: tuple[ResearchAction, ...], *,
              retro_receipts: dict[str, str], retro_complete: dict[str, bool] | None = None,
              first_break_counts: dict[str, int], revival_ids: set[str] | None = None) -> RouteCertificate:
    revival_ids = revival_ids or set()
    retro_complete = retro_complete or {}
    admissible: list[ResearchAction] = []
    rejected: list[str] = []

    for action in actions:
        blockers = _admissibility_blockers(
            action,
            retro_receipt_id=retro_receipts.get(action.action_id),
            retro_search_complete=retro_complete.get(action.action_id),
            first_break_count=first_break_counts.get(action.action_id, 0),
            revival_ids=revival_ids,
        )
        if blockers:
            rejected.append(f"{action.action_id}: {';'.join(blockers)}")
        else:
            admissible.append(action)

    if not admissible:
        return RouteCertificate(
            frontier_id=state.frontier_id,
            selected_action=None,
            score=None,
            disposition=Disposition.ABSTAIN,
            rationale=("No admissible action survived fail-closed routing.", *rejected),
            retro_receipt_ids=tuple(sorted(set(retro_receipts.values()))),
            surviving_objections=(),
            required_relock=("establish missing control contracts",),
        )

    ranked = sorted(admissible, key=lambda a: (-action_score(a), a.action_id))
    selected = ranked[0]
    rationale = (
        "selected highest deterministic information/falsification/closure score among admissible actions",
        f"score={action_score(selected):.3f}",
        *tuple(f"rejected {item}" for item in rejected),
    )
    required_relock: list[str] = []
    if selected.decision_commutation_required:
        required_relock.append("decision commutation before decision-bearing use")
    if selected.horizon_required_for_tail_claim:
        required_relock.append("horizon certificate before any tail claim")

    return RouteCertificate(
        frontier_id=state.frontier_id,
        selected_action=selected.action_id,
        score=action_score(selected),
        disposition=Disposition.CONTINUE,
        rationale=rationale,
        retro_receipt_ids=(retro_receipts[selected.action_id],) if selected.action_id in retro_receipts else (),
        surviving_objections=selected.surviving_objections,
        required_relock=tuple(required_relock),
    )
