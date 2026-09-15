#!/usr/bin/env python3
"""Probe the exact frozen #186 schedule for selector variables only.

This artifact intentionally contains no domination-margin target labels.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from canonical_source_arb import ball_record, set_precision
from post187_fb05_q14_mixed_drift_selector import selector_record_from_box
from probe_post185_fb05_q13_remainder_drift_scope import frozen_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post185_fb05_q13_remainder_drift_v1.json"


def _serialize_values(values: dict) -> dict:
    return {
        key: (None if value is None else ball_record(value))
        for key, value in values.items()
    }


def selector_schedule(fixture: dict) -> dict:
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))
    inherited = frozen_schedule(source)
    if fixture["source_fixture"] != SOURCE_FIXTURE.name:
        raise AssertionError("post-#187 source fixture drift")
    if inherited["primary_box_count"] != int(fixture["expected_primary_box_count"]):
        raise AssertionError("post-#187 inherited primary count regression")
    if inherited["control_box_count"] != int(fixture["expected_control_box_count"]):
        raise AssertionError("post-#187 inherited control count regression")
    if source["selected_target"] != fixture["selected_target"]:
        raise AssertionError("post-#187 inherited target drift")
    return {
        "schema_version": "POST187_FB05_Q14_MIXED_DRIFT_SELECTOR_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_FROZEN_SELECTOR_SCHEDULE_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "source_schedule_schema_version": inherited["schema_version"],
        "source_fixture_schema_version": source["schema_version"],
        "primary_box_count": inherited["primary_box_count"],
        "control_box_count": inherited["control_box_count"],
        "boxes": inherited["boxes"],
        "candidate_rule_ids": [r["id"] for r in fixture["candidate_rules"]],
        "target_labels_included": False,
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST187_Q14_SELECTOR_SCHEDULE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    set_precision(int(fixture["arb_precision_bits"]))
    out = selector_schedule(fixture)
    records = []
    for box in out["boxes"]:
        rec = selector_record_from_box(box)
        records.append({
            "label": rec["label"],
            "Q": rec["Q"],
            "role": rec["role"],
            "primary": rec["primary"],
            "side": rec["side"],
            "offset_bit": rec["offset_bit"],
            "scope": rec["scope"],
            "candidate_values": _serialize_values(rec["candidates"]),
            "diagnostics": _serialize_values(rec["diagnostics"]),
            "implementation_checks": rec["checks"],
        })
    out["selector_records"] = records
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "primary_box_count": out["primary_box_count"],
        "control_box_count": out["control_box_count"],
        "candidate_rule_count": len(out["candidate_rule_ids"]),
        "target_labels_included": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
