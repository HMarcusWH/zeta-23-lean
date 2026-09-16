#!/usr/bin/env python3
"""Freeze the post-#196 one-cell replay schedule without changing #195 scope."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from probe_post194_fb05_q14_parity_trajectory_sharp_enclosure_scope import (
    sharp_trajectory_schedule,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post196_fb05_q14_residual_cell_replay_v1.json"


def residual_replay_schedule(fixture: dict) -> dict:
    source_path = HERE / "fixtures" / fixture["inherited_post195_fixture"]
    source = json.loads(source_path.read_text(encoding="utf-8"))
    inherited = sharp_trajectory_schedule(source)

    for key in ("selected_target", "required_ancestry_control", "arb_precision_bits", "max_refinement_depth", "max_evaluated_cells"):
        if fixture[key] != inherited[key]:
            raise AssertionError(f"post-#196 residual replay inherited scope drift: {key}")

    return {
        "schema_version": "POST196_FB05_Q14_RESIDUAL_CELL_REPLAY_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "base_main_sha": fixture["base_main_sha"],
        "base_main_tree": fixture["base_main_tree"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_authority_pr": fixture["research_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "inherited_post195_schedule_schema": inherited["schema_version"],
        "selected_target": inherited["selected_target"],
        "required_ancestry_control": inherited["required_ancestry_control"],
        "arb_precision_bits": inherited["arb_precision_bits"],
        "max_refinement_depth": inherited["max_refinement_depth"],
        "max_evaluated_cells": inherited["max_evaluated_cells"],
        "followup_evaluated_cells": fixture["followup_evaluated_cells"],
        "boxes": inherited["boxes"],
        "primary_box_count": inherited["primary_box_count"],
        "control_box_count": inherited["control_box_count"],
        "primary_hull": inherited["primary_hull"],
        "policy": fixture["policy"],
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST196_FB05_Q14_RESIDUAL_CELL_REPLAY_SCHEDULE.json"),
    )
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = residual_replay_schedule(fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "primary_hull": out["primary_hull"],
        "max_evaluated_cells": out["max_evaluated_cells"],
        "followup_evaluated_cells": out["followup_evaluated_cells"],
        "one_cell_followup_only": out["policy"]["one_cell_followup_only"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
