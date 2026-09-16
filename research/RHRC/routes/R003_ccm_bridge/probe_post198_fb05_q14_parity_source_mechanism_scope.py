#!/usr/bin/env python3
"""Freeze the post-#198 Q14 parity source-mechanism schedule."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from probe_post196_fb05_q14_residual_cell_replay_scope import residual_replay_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post198_fb05_q14_parity_source_mechanism_v1.json"


def mechanism_schedule(fixture: dict) -> dict:
    inherited_fixture = json.loads((HERE / "fixtures" / fixture["inherited_post197_fixture"]).read_text(encoding="utf-8"))
    inherited = residual_replay_schedule(inherited_fixture)
    if fixture["selected_target"] != inherited["selected_target"]:
        raise AssertionError("post-#198 selected target drift")
    if fixture["required_ancestry_control"] != inherited["required_ancestry_control"]:
        raise AssertionError("post-#198 ancestry control drift")
    if int(fixture["arb_precision_bits"]) != int(inherited["arb_precision_bits"]):
        raise AssertionError("post-#198 precision drift")
    return {
        "schema_version": "POST198_FB05_Q14_PARITY_SOURCE_MECHANISM_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "base_main_sha": fixture["base_main_sha"],
        "base_main_tree": fixture["base_main_tree"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_authority_pr": fixture["research_authority_pr"],
        "research_authority_head_sha": fixture["research_authority_head_sha"],
        "research_authority_merge_sha": fixture["research_authority_merge_sha"],
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
        "four_way_channels": fixture["four_way_channels"],
        "collapsed_channels": fixture["collapsed_channels"],
        "policy": fixture["policy"],
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST198_FB05_Q14_PARITY_SOURCE_MECHANISM_SCHEDULE.json"))
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = mechanism_schedule(fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "primary_hull": out["primary_hull"],
        "primary_box_count": out["primary_box_count"],
        "control_box_count": out["control_box_count"],
        "four_way_channels": out["four_way_channels"],
        "collapsed_channels": out["collapsed_channels"],
        "control_blind_mechanism_selection_required": out["policy"]["control_blind_mechanism_selection_required"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
