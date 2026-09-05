from __future__ import annotations

import json
from pathlib import Path

from control_v2.schemas import ResearchState, ResidualVector, TheoremAnchor

RHRC = Path(__file__).resolve().parents[1]


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def load_research_state() -> ResearchState:
    control = _load_json(RHRC / "control_v2" / "CONTROL_STATE.json")
    actions = _load_json(RHRC / "control_v2" / "ACTION_REGISTRY.json")
    boundary = _load_json(RHRC / "BOUNDARY.json")

    if control["boundary_id"] != boundary["boundary_id"]:
        raise ValueError("Control v2 boundary_id does not match BOUNDARY.json")
    if control["terminal_claim"] != "RH_OPEN":
        raise ValueError("Control v2 may only run with terminal_claim=RH_OPEN")

    raw_anchor = control["merged_theorem_anchor"]
    anchor = TheoremAnchor(
        pr=int(raw_anchor["pr"]),
        merge_commit=str(raw_anchor["merge_commit"]),
        tree=str(raw_anchor["tree"]),
        status=str(raw_anchor["status"]),
    )

    return ResearchState(
        boundary_id=control["boundary_id"],
        terminal_claim=control["terminal_claim"],
        anchor=anchor,
        frontier_id=actions["current_frontier"],
        open_obligations=tuple(actions["open_obligations"]),
        residuals=ResidualVector(),
    )
