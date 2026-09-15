#!/usr/bin/env python3
"""Emit the frozen exact-rational semantic-independence witness schedule.

The schedule contains abstract normalized selector states only.  It contains no
canonical production labels, no fitted thresholds, and no source-target joins.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post188_fb05_q14_mixed_drift_selector_independence_v1.json"
SOURCE_SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"


def independence_schedule(fixture: dict, selector_fixture: dict) -> dict:
    source_ids = [row["id"] for row in selector_fixture["candidate_rules"]]
    witness_ids = [row["id"] for row in fixture["candidate_witnesses"]]
    if source_ids != witness_ids:
        raise AssertionError("semantic-independence schedule candidate registry drift")
    return {
        "schema_version": "POST188_FB05_Q14_SELECTOR_SEMANTIC_INDEPENDENCE_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "mixed_drift_falsification_pr": fixture["mixed_drift_falsification_pr"],
        "selector_audit_pr": fixture["selector_audit_pr"],
        "selector_head_sha": fixture["selector_head_sha"],
        "selector_merge_sha": fixture["selector_merge_sha"],
        "source_selector_fixture_schema_version": selector_fixture["schema_version"],
        "candidate_rule_ids": source_ids,
        "candidate_witnesses": fixture["candidate_witnesses"],
        "target_alias_controls": fixture["target_alias_controls"],
        "target_alias_states": fixture["target_alias_states"],
        "canonical_production_labels_included": False,
        "threshold_refitting_permitted": False,
        "canonical_realizability_claimed": False,
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST188_Q14_SELECTOR_INDEPENDENCE_SCHEDULE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SOURCE_SELECTOR_FIXTURE.read_text(encoding="utf-8"))
    out = independence_schedule(fixture, selector_fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "candidate_witness_count": len(out["candidate_witnesses"]),
        "target_alias_control_count": len(out["target_alias_controls"]),
        "canonical_production_labels_included": False,
        "threshold_refitting_permitted": False,
        "canonical_realizability_claimed": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
