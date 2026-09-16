#!/usr/bin/env python3
"""Freeze the post-#202 composite parity-gap schedule from exact #201 ancestry."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from probe_post200_fb05_q14_discrepancy_mechanism_scope import discrepancy_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post202_fb05_q14_composite_parity_gap_v1.json"


def composite_schedule(fixture: dict) -> dict:
    inherited_fixture = json.loads(
        (HERE / "fixtures" / fixture["inherited_post201_fixture"]).read_text(encoding="utf-8")
    )
    inherited = discrepancy_schedule(inherited_fixture)
    if fixture["selected_target"] != inherited["selected_target"]:
        raise AssertionError("post-#202 selected target drift")
    if fixture["required_ancestry_control"] != inherited["required_ancestry_control"]:
        raise AssertionError("post-#202 ancestry control drift")
    if int(fixture["arb_precision_bits"]) != int(inherited["arb_precision_bits"]):
        raise AssertionError("post-#202 precision drift")
    return {
        "schema_version": "POST202_FB05_Q14_COMPOSITE_PARITY_GAP_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "base_main_sha": fixture["base_main_sha"],
        "base_main_tree": fixture["base_main_tree"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_authority_pr": fixture["research_authority_pr"],
        "research_authority_head_sha": fixture["research_authority_head_sha"],
        "research_authority_merge_sha": fixture["research_authority_merge_sha"],
        "research_authority_tree_sha": fixture["research_authority_tree_sha"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "selected_target": inherited["selected_target"],
        "required_ancestry_control": inherited["required_ancestry_control"],
        "arb_precision_bits": inherited["arb_precision_bits"],
        "max_refinement_depth": inherited["max_refinement_depth"],
        "max_evaluated_cells": inherited["max_evaluated_cells"],
        "followup_evaluated_cells": inherited["followup_evaluated_cells"],
        "boxes": inherited["boxes"],
        "primary_box_count": inherited["primary_box_count"],
        "control_box_count": inherited["control_box_count"],
        "primary_hull": inherited["primary_hull"],
        "center_kill_switch_pattern": fixture["center_kill_switch_pattern"],
        "policy": fixture["policy"],
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST202_FB05_Q14_COMPOSITE_PARITY_GAP_SCHEDULE.json"),
    )
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = composite_schedule(fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "primary_hull": out["primary_hull"],
        "primary_box_count": out["primary_box_count"],
        "control_box_count": out["control_box_count"],
        "center_kill_switch_pattern": out["center_kill_switch_pattern"],
        "precision_bits": out["arb_precision_bits"],
        "center_gate_before_full_cover_required": out["policy"]["center_gate_before_full_cover_required"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
