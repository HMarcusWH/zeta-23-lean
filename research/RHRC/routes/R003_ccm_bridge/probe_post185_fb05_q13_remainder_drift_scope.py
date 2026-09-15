#!/usr/bin/env python3
"""Reconstruct the exact frozen #180 schedule for post-#185 remainder-drift work.

Discovery only. The schedule is inherited exactly; no mathematical disposition
is certified here.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from probe_post179_fb05_q13_correlation_preserving_derivative_scope import inherited_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post185_fb05_q13_remainder_drift_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post179_fb05_q13_correlation_preserving_derivative_v1.json"


def frozen_schedule(fixture: dict) -> dict:
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))
    inherited = inherited_schedule(source)
    boxes = inherited["boxes"]

    primary_count = sum(1 for b in boxes if b["primary"])
    control_count = len(boxes) - primary_count
    if primary_count != int(fixture["expected_primary_box_count"]):
        raise AssertionError("inherited primary box count regression")
    if control_count != int(fixture["expected_control_box_count"]):
        raise AssertionError("inherited control box count regression")
    if source["selected_target"] != fixture["selected_target"]:
        raise AssertionError("inherited target drift")

    return {
        "schema_version": "POST185_FB05_Q13_REMAINDER_DRIFT_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_INHERITED_REMAINDER_DRIFT_SCHEDULE_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "source_schedule_schema_version": inherited["schema_version"],
        "source_fixture_schema_version": source["schema_version"],
        "boxes": boxes,
        "primary_box_count": primary_count,
        "control_box_count": control_count,
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST185_Q14_REMAINDER_DRIFT_SCHEDULE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = frozen_schedule(fixture)
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
