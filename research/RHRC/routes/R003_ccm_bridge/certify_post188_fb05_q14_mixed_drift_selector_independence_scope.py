#!/usr/bin/env python3
"""Certify exact rational semantic-independence countermodels for post-#188.

Green means the frozen candidate registry is faithfully replayed, every
individual selector has an exact separating pair in the audited normalized
algebra, and deliberate target aliases are correctly detected as circular.
No canonical arithmetic realizability is claimed.  RH remains OPEN.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post188_fb05_q14_mixed_drift_selector_independence import (
    FILTERING_CLASSIFICATION,
    TARGET_EQUIVALENT_CLASSIFICATION,
    audit_fixture,
)
from probe_post188_fb05_q14_mixed_drift_selector_independence_scope import (
    independence_schedule,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post188_fb05_q14_mixed_drift_selector_independence_v1.json"
SOURCE_SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"


def _validate_schedule(fixture: dict, selector_fixture: dict, schedule: dict) -> None:
    expected = independence_schedule(fixture, selector_fixture)
    keys = (
        "schema_version",
        "status",
        "claim_cap",
        "theorem_authority_pr",
        "mixed_drift_falsification_pr",
        "selector_audit_pr",
        "selector_head_sha",
        "selector_merge_sha",
        "source_selector_fixture_schema_version",
        "candidate_rule_ids",
        "candidate_witnesses",
        "target_alias_controls",
        "target_alias_states",
        "canonical_production_labels_included",
        "threshold_refitting_permitted",
        "canonical_realizability_claimed",
    )
    for key in keys:
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"semantic-independence schedule drift: {key}")
    if schedule["canonical_production_labels_included"] is not False:
        raise AssertionError("abstract witness schedule leaked canonical production labels")
    if schedule["threshold_refitting_permitted"] is not False:
        raise AssertionError("semantic audit permitted threshold refitting")
    if schedule["canonical_realizability_claimed"] is not False:
        raise AssertionError("semantic audit overclaimed canonical realizability")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST188_Q14_SELECTOR_INDEPENDENCE_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SOURCE_SELECTOR_FIXTURE.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, selector_fixture, schedule)

    result = audit_fixture(selector_fixture, fixture)
    source_ids = [row["id"] for row in selector_fixture["candidate_rules"]]
    if result["status"] != "PASS":
        raise AssertionError("semantic-independence certification unresolved")
    if result["abstractly_separable_candidate_ids"] != source_ids:
        raise AssertionError("semantic-independence result order/coverage drift")
    if result["unresolved_candidate_ids"]:
        raise AssertionError("candidate semantic-independence unresolved")
    for row in result["candidate_results"]:
        if row["classification"] != FILTERING_CLASSIFICATION:
            raise AssertionError(f"candidate not abstractly separable: {row['id']}")
        if not row["same_candidate_value"]:
            raise AssertionError(f"candidate value not held fixed exactly: {row['id']}")
        if not row["same_nonboundary_threshold_side"]:
            raise AssertionError(f"candidate threshold side not held fixed: {row['id']}")
        if not row["target_sign_flip"]:
            raise AssertionError(f"target sign did not flip: {row['id']}")
        if row["canonical_realizability_claimed"]:
            raise AssertionError(f"canonical realizability overclaim: {row['id']}")

    for row in result["target_alias_controls"]:
        if row["classification"] != TARGET_EQUIVALENT_CLASSIFICATION:
            raise AssertionError(f"target-alias positive control failed: {row['id']}")
        if any(residual != "0" for residual in row["identity_residuals"]):
            raise AssertionError(f"target-alias residual nonzero: {row['id']}")

    out = {
        "schema_version": "POST188_FB05_Q14_SELECTOR_SEMANTIC_INDEPENDENCE_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "provenance": {
            "theorem_authority_pr": fixture["theorem_authority_pr"],
            "mixed_drift_falsification_pr": fixture["mixed_drift_falsification_pr"],
            "selector_audit_pr": fixture["selector_audit_pr"],
            "selector_head_sha": fixture["selector_head_sha"],
            "selector_merge_sha": fixture["selector_merge_sha"],
        },
        "result": result,
        "interpretation": {
            "candidate_result": "Each individual frozen post-#188 selector is abstractly separable from the domination-target sign in the audited normalized algebra.",
            "positive_control_result": "Deliberate mechanism/channel target aliases are detected as exact semantic target equivalents.",
            "next_question": "Whether canonical arithmetic CCM states satisfy extra constraints that destroy these abstract countermodels remains open.",
        },
        "nonclaims": fixture["nonclaims"],
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "abstractly_separable_candidate_count": len(result["abstractly_separable_candidate_ids"]),
        "semantic_target_equivalent_control_count": len(result["target_alias_controls"]),
        "canonical_realizability_claimed": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
