#!/usr/bin/env python3
"""Freeze the post-#190 canonical-realizability audit schedule."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post190_fb05_canonical_realizability import LAYER_IDS
from probe_post185_fb05_q13_remainder_drift_scope import frozen_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post190_fb05_canonical_realizability_v1.json"
SOURCE_SCHEDULE_FIXTURE = HERE / "fixtures" / "post185_fb05_q13_remainder_drift_v1.json"


def canonical_realizability_schedule(fixture: dict) -> dict:
    source = json.loads(SOURCE_SCHEDULE_FIXTURE.read_text(encoding="utf-8"))
    inherited = frozen_schedule(source)
    if fixture["selected_target"] != source["selected_target"]:
        raise AssertionError("post-#190 selected target drift")
    if fixture["required_layer_ids"] != list(LAYER_IDS):
        raise AssertionError("post-#190 layer registry drift")
    if inherited["primary_box_count"] != int(fixture["expected_primary_box_count"]):
        raise AssertionError("post-#190 primary box count drift")
    if inherited["control_box_count"] != int(fixture["expected_control_box_count"]):
        raise AssertionError("post-#190 control box count drift")
    return {
        "schema_version": "POST190_FB05_CANONICAL_REALIZABILITY_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "base_main_sha": fixture["base_main_sha"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_authority_pr": fixture["research_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "selected_target": fixture["selected_target"],
        "required_ancestry_control": fixture["required_ancestry_control"],
        "arb_precision_bits": fixture["arb_precision_bits"],
        "layer_ids": list(LAYER_IDS),
        "boxes": inherited["boxes"],
        "primary_box_count": inherited["primary_box_count"],
        "control_box_count": inherited["control_box_count"],
        "policy": fixture["policy"],
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST190_FB05_CANONICAL_REALIZABILITY_SCHEDULE.json"),
    )
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = canonical_realizability_schedule(fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "layer_count": len(out["layer_ids"]),
        "primary_box_count": out["primary_box_count"],
        "control_box_count": out["control_box_count"],
        "primary_labels": [b["label"] for b in out["boxes"] if b["primary"]],
        "adaptive_center_movement_permitted": out["policy"]["adaptive_center_movement_permitted"],
        "new_q_n_parity_search_permitted": out["policy"]["new_q_n_parity_search_permitted"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
