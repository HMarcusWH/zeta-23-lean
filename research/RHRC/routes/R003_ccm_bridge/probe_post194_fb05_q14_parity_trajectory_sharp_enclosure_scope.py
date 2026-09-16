#!/usr/bin/env python3
"""Freeze the post-#194 sharp Q14 parity-trajectory schedule."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import primary_hull
from probe_post177_fb05_q13_fixed_unit_derivative_scope import expected_boxes

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post194_fb05_q14_parity_trajectory_sharp_enclosure_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def sharp_trajectory_schedule(fixture: dict) -> dict:
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))
    if fixture["selected_target"] != source["selected_target"]:
        raise AssertionError("post-#194 selected target drift")
    if fixture["required_ancestry_control"] != source["required_ancestry_control"]:
        raise AssertionError("post-#194 ancestry control drift")

    boxes = expected_boxes(source)
    primary_count = sum(1 for box in boxes if bool(box["primary"]))
    control_count = sum(1 for box in boxes if not bool(box["primary"]))
    if primary_count != int(fixture["expected_primary_box_count"]):
        raise AssertionError("post-#194 primary box count drift")
    if control_count != int(fixture["expected_control_box_count"]):
        raise AssertionError("post-#194 control box count drift")

    hull = primary_hull(boxes)
    if int(hull["Q"]) != int(fixture["selected_target"]["primary_Q"]):
        raise AssertionError("post-#194 primary hull Q drift")

    return {
        "schema_version": "POST194_FB05_Q14_PARITY_TRAJECTORY_SHARP_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "base_main_sha": fixture["base_main_sha"],
        "base_main_tree": fixture["base_main_tree"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_authority_pr": fixture["research_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "selected_target": fixture["selected_target"],
        "required_ancestry_control": fixture["required_ancestry_control"],
        "arb_precision_bits": fixture["arb_precision_bits"],
        "max_refinement_depth": fixture["max_refinement_depth"],
        "max_evaluated_cells": fixture["max_evaluated_cells"],
        "boxes": boxes,
        "primary_box_count": primary_count,
        "control_box_count": control_count,
        "primary_hull": hull,
        "policy": fixture["policy"],
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST194_FB05_Q14_PARITY_TRAJECTORY_SHARP_SCHEDULE.json"),
    )
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = sharp_trajectory_schedule(fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": "PASS",
                "primary_box_count": out["primary_box_count"],
                "control_box_count": out["control_box_count"],
                "primary_hull": out["primary_hull"],
                "max_refinement_depth": out["max_refinement_depth"],
                "max_evaluated_cells": out["max_evaluated_cells"],
                "shared_cell_abc_comparison_required": out["policy"][
                    "shared_cell_abc_comparison_required"
                ],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
