from __future__ import annotations

import json
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
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

    boundary_source = json.loads((RHRC / "BOUNDARY.json").read_text(encoding="utf-8"))
    diagnostic = boundary_source["diagnostic_engine"]
    route_engine = boundary_source["route_closure_engine"]
    if by_id["FFBBP_RUNTIME"]["version"] != diagnostic["reference_architecture_version"]:
        raise SystemExit("integration_lint: FFBBP runtime version drift from BOUNDARY.json")
    if by_id["FFBBP_RUNTIME"]["scope"] != diagnostic["qualification_scope"]:
        raise SystemExit("integration_lint: FFBBP runtime qualification scope drift")
    if by_id["OOL_MVS"]["version"] != route_engine["kernel_version"]:
        raise SystemExit("integration_lint: OoL-MVS version drift from BOUNDARY.json")
    if by_id["OOL_MVS"]["scope"] != route_engine["import_scope"]:
        raise SystemExit("integration_lint: OoL-MVS import scope drift")

    ffbbp_v16 = json.loads(
        (RHRC / "ffbbp" / "FFBBP_V16_ASSURANCE_REFERENCE.json").read_text(encoding="utf-8")
    )
    if by_id["FFBBP_ASSURANCE"]["version"] != ffbbp_v16["theory_version"]:
        raise SystemExit("integration_lint: FFBBP v1.6 theory version drift")
    if ffbbp_v16.get("inherits_run42c_qualification") is not False:
        raise SystemExit("integration_lint: source FFBBP v1.6 overlay qualification drift")

    ool_reference = json.loads(
        (RHRC / "ool" / "OOL_REFERENCE.json").read_text(encoding="utf-8")
    )
    if by_id["OOL_MVS"]["version"] != ool_reference["version"]:
        raise SystemExit("integration_lint: OoL reference version drift")

    host_toolchain = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip()
    if not host_toolchain.endswith(by_id["PERMANSSON_EXTERNAL"]["host_lean_toolchain"]):
        raise SystemExit("integration_lint: recorded host Lean toolchain drift")

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
