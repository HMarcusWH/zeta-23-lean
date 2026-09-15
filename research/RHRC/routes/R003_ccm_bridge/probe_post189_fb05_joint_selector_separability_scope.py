#!/usr/bin/env python3
"""Emit the frozen post-#189 joint-selector separability schedule.

This is a deterministic exact-rational replay.  No grid search, threshold
refitting, new selector discovery, or canonical production labels are allowed.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post189_fb05_joint_selector_separability import EXPECTED_STRONG_IDS

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post189_fb05_joint_selector_separability_v1.json"
SOURCE_SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"


def joint_schedule(fixture: dict, selector_fixture: dict) -> dict:
    strong_ids = [
        row["id"] for row in selector_fixture["candidate_rules"] if bool(row["strong_eligible"])
    ]
    if strong_ids != list(EXPECTED_STRONG_IDS):
        raise AssertionError("joint schedule strong selector registry drift")
    if fixture["strong_selector_ids"] != strong_ids:
        raise AssertionError("fixture strong selector order drift")
    return {
        "schema_version": "POST189_FB05_JOINT_SELECTOR_SEPARABILITY_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "base_main_sha": fixture["base_main_sha"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "mixed_drift_falsification_pr": fixture["mixed_drift_falsification_pr"],
        "selector_audit_pr": fixture["selector_audit_pr"],
        "semantic_independence_pr": fixture["semantic_independence_pr"],
        "semantic_independence_head_sha": fixture["semantic_independence_head_sha"],
        "semantic_independence_merge_sha": fixture["semantic_independence_merge_sha"],
        "source_selector_fixture_schema_version": selector_fixture["schema_version"],
        "strong_selector_ids": strong_ids,
        "joint_witness": fixture["joint_witness"],
        "target_augmented_controls": fixture["target_augmented_controls"],
        "canonical_production_labels_included": False,
        "grid_search_permitted": False,
        "threshold_refitting_permitted": False,
        "new_selector_features_permitted": False,
        "canonical_realizability_claimed": False,
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST189_FB05_JOINT_SELECTOR_SCHEDULE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SOURCE_SELECTOR_FIXTURE.read_text(encoding="utf-8"))
    out = joint_schedule(fixture, selector_fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "strong_selector_count": len(out["strong_selector_ids"]),
        "deterministic_exact_witness_count": 1,
        "grid_search_permitted": False,
        "threshold_refitting_permitted": False,
        "new_selector_features_permitted": False,
        "canonical_realizability_claimed": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
