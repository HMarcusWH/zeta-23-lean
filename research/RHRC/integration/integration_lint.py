from __future__ import annotations

import json
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
INTEGRATION = RHRC / "integration"


def load(name: str) -> dict:
    return json.loads((INTEGRATION / name).read_text(encoding="utf-8"))


def main() -> int:
    state = load("INTEGRATION_STATE.json")
    boundary = load("INTEGRATION_BOUNDARY.json")
    frameworks = load("FRAMEWORK_REGISTRY.json")

    for name, data in (
        ("state", state),
        ("boundary", boundary),
        ("framework registry", frameworks),
    ):
        if data.get("terminal_claim") != "RH_OPEN":
            raise SystemExit(f"integration_lint: {name} does not preserve RH_OPEN")

    if state["theorem_authority"]["pr"] != 262:
        raise SystemExit("integration_lint: theorem authority must remain PR #262")
    if state["frozen_control_authority"]["pr"] != 117:
        raise SystemExit("integration_lint: frozen control authority must remain PR #117")
    if state["repository_graph_authority"]["pr"] != 263:
        raise SystemExit("integration_lint: graph authority must remain PR #263")
    if state.get("theorem_promotion") is not False:
        raise SystemExit("integration_lint: integration state attempts theorem promotion")
    if boundary["claim_firewall"].get("theorem_promotion") is not False:
        raise SystemExit("integration_lint: integration boundary attempts theorem promotion")

    by_id = {row["id"]: row for row in frameworks["frameworks"]}
    required = {
        "FFBBP_RUNTIME",
        "FFBBP_ASSURANCE",
        "OOL_MVS",
        "PERMANSSON_EMBEDDED",
        "PERMANSSON_EXTERNAL",
        "MCM_HMWH",
    }
    if set(by_id) != required:
        raise SystemExit(
            "integration_lint: framework registry drift "
            f"missing={sorted(required - set(by_id))} extra={sorted(set(by_id) - required)}"
        )
    if by_id["FFBBP_ASSURANCE"].get("inherits_run42c_qualification") is not False:
        raise SystemExit("integration_lint: FFBBP v1.6 may not inherit RUN42C qualification")
    if by_id["MCM_HMWH"]["status"] != "NOT_YET_INTEGRATED":
        raise SystemExit("integration_lint: MCM-HMWH must remain not-yet-integrated in foundation PR")

    summary = INTEGRATION / "generated" / "SOURCE_CANDIDATE_SUMMARY.json"
    if summary.exists():
        data = json.loads(summary.read_text(encoding="utf-8"))
        if data.get("terminal_claim") != "RH_OPEN":
            raise SystemExit("integration_lint: candidate summary does not preserve RH_OPEN")
        if data.get("theorem_promotion") is not False:
            raise SystemExit("integration_lint: candidate summary attempts theorem promotion")

    print("RHRC INTEGRATION LINT: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
