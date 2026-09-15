#!/usr/bin/env python3
"""Plumbing/provenance checks for the post-#188 selector independence audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post188_fb05_q14_mixed_drift_selector_independence import (
    FILTERING_CLASSIFICATION,
    TARGET_EQUIVALENT_CLASSIFICATION,
    audit_fixture,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post188_fb05_q14_mixed_drift_selector_independence_v1.json"
SOURCE_SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"
SOURCE_SELECTOR_MODULE = HERE / "post187_fb05_q14_mixed_drift_selector.py"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SOURCE_SELECTOR_FIXTURE.read_text(encoding="utf-8"))

    if fixture["schema_version"] != "POST188_FB05_Q14_SELECTOR_SEMANTIC_INDEPENDENCE_FIXTURE_v1":
        raise AssertionError("semantic-independence fixture schema drift")
    if int(fixture["selector_audit_pr"]) != 188:
        raise AssertionError("selector authority PR drift")
    if fixture["selector_head_sha"] != "a63cc3092dc1a8bda6aa89d9face659fd0e6fb5b":
        raise AssertionError("selector head provenance drift")
    if fixture["selector_merge_sha"] != "55fb2f1a1a344c3b752d800853f4f92985c80cd1":
        raise AssertionError("selector merge provenance drift")
    if fixture["source_selector_fixture"] != SOURCE_SELECTOR_FIXTURE.name:
        raise AssertionError("source selector fixture path drift")
    if fixture["source_selector_module"] != SOURCE_SELECTOR_MODULE.name:
        raise AssertionError("source selector module path drift")
    if git_blob_sha(SOURCE_SELECTOR_FIXTURE) != fixture["source_selector_fixture_blob_sha"]:
        raise AssertionError("post-#188 selector fixture content drift")
    if git_blob_sha(SOURCE_SELECTOR_MODULE) != fixture["source_selector_module_blob_sha"]:
        raise AssertionError("post-#188 selector implementation content drift")

    source_text = SOURCE_SELECTOR_MODULE.read_text(encoding="utf-8")
    if "from post185_fb05_q13_remainder_drift" in source_text or "import post185_fb05_q13_remainder_drift" in source_text:
        raise AssertionError("post-#188 selector target firewall regressed")

    source_ids = [row["id"] for row in selector_fixture["candidate_rules"]]
    witness_ids = [row["id"] for row in fixture["candidate_witnesses"]]
    if witness_ids != source_ids:
        raise AssertionError("semantic witness order/registry drift from post-#188 selectors")
    if len(set(witness_ids)) != len(witness_ids):
        raise AssertionError("duplicate semantic witness id")

    if fixture["required_candidate_classification"] != FILTERING_CLASSIFICATION:
        raise AssertionError("candidate classification policy drift")
    if fixture["required_target_alias_classification"] != TARGET_EQUIVALENT_CLASSIFICATION:
        raise AssertionError("target-alias classification policy drift")

    result = audit_fixture(selector_fixture, fixture)
    if result["status"] != "PASS":
        raise AssertionError("semantic-independence audit did not classify decisively")
    if result["unresolved_candidate_ids"]:
        raise AssertionError("unresolved post-#188 selector candidate")
    if result["failed_target_alias_control_ids"]:
        raise AssertionError("semantic target-alias positive control failed")
    if len(result["abstractly_separable_candidate_ids"]) != len(source_ids):
        raise AssertionError("not every frozen selector received an exact separating pair")
    if result["theorem_promotion"] or result["canonical_realizability_claimed"]:
        raise AssertionError("research claim firewall regression")
    if result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("terminal claim firewall regression")

    print(json.dumps({
        "status": "PASS",
        "selector_candidate_count": len(source_ids),
        "abstractly_separable_count": len(result["abstractly_separable_candidate_ids"]),
        "target_alias_positive_control_count": len(result["target_alias_controls"]),
        "source_fixture_blob_locked": True,
        "source_module_blob_locked": True,
        "canonical_realizability_claimed": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
