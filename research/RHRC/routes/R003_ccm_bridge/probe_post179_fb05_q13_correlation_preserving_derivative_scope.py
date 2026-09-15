#!/usr/bin/env python3
"""Reconstruct the exact inherited #178 derivative schedule for post-#179 work.

Discovery only. No mathematical disposition is certified here.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from probe_post177_fb05_q13_fixed_unit_derivative_scope import expected_boxes

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post179_fb05_q13_correlation_preserving_derivative_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def inherited_schedule(fixture: dict) -> dict:
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))
    boxes = expected_boxes(source)
    primary_count = sum(1 for b in boxes if b["primary"])
    control_count = len(boxes) - primary_count
    if primary_count != int(fixture["expected_primary_box_count"]):
        raise AssertionError("inherited primary box count regression")
    if control_count != int(fixture["expected_control_box_count"]):
        raise AssertionError("inherited control box count regression")
    if source["selected_target"] != fixture["selected_target"]:
        raise AssertionError("inherited derivative target drift")

    return {
        "schema_version": "POST179_FB05_Q13_CORRELATION_PRESERVING_DERIVATIVE_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_INHERITED_DERIVATIVE_SCHEDULE_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "source_fixture_schema_version": source["schema_version"],
        "boxes": boxes,
        "primary_box_count": primary_count,
        "control_box_count": control_count,
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST179_Q14_CORRELATION_SCHEDULE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = inherited_schedule(fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "primary_box_count": out["primary_box_count"],
        "control_box_count": out["control_box_count"],
        "primary_labels": [b["label"] for b in out["boxes"] if b["primary"]],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
