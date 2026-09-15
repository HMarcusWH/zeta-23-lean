#!/usr/bin/env python3
"""Plumbing/provenance guards for the post-#189 joint-selector audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post189_fb05_joint_selector_separability import (
    EXACT_VECTOR_CLASSIFICATION,
    EXPECTED_STRONG_IDS,
    TARGET_AUGMENTED_CLASSIFICATION,
    THRESHOLD_SIGNATURE_CLASSIFICATION,
    audit_fixture,
    strong_rules,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post189_fb05_joint_selector_separability_v1.json"
SOURCE_SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"
SOURCE_SELECTOR_MODULE = HERE / "post187_fb05_q14_mixed_drift_selector.py"
SOURCE_INDEPENDENCE_FIXTURE = HERE / "fixtures" / "post188_fb05_q14_mixed_drift_selector_independence_v1.json"
SOURCE_INDEPENDENCE_MODULE = HERE / "post188_fb05_q14_mixed_drift_selector_independence.py"

EXPECTED_STRONG_FIELDS = (
    "coupling_ratio",
    "parity_predecessor_ratio",
    "parity_log_slope_gap",
    "chi_prime_signed",
    "chi_arch_signed",
    "chi_pole",
    "prime_vs_smooth_sq_ratio",
)
EXPECTED_DIAGNOSTIC_IDS = (
    "R1_PREDECESSOR_REMAINDER_COMPONENT",
    "R2_CROSS_REMAINDER_COMPONENT",
    "R3_SHELL_REMAINDER_COMPONENT",
)


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SOURCE_SELECTOR_FIXTURE.read_text(encoding="utf-8"))

    if fixture["schema_version"] != "POST189_FB05_JOINT_SELECTOR_SEPARABILITY_FIXTURE_v1":
        raise AssertionError("joint-selector fixture schema drift")
    if fixture["claim_cap"] != "ABSTRACT_JOINT_STRONG_SELECTOR_SEPARABILITY_ONLY":
        raise AssertionError("joint-selector claim cap drift")
    if fixture["base_main_sha"] != "2e4cd7b3f170612fe05ad7c334dee504304d8746":
        raise AssertionError("post-#189 base/main provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184:
        raise AssertionError("theorem authority drift")
    if int(fixture["mixed_drift_falsification_pr"]) != 186:
        raise AssertionError("mixed-drift falsification provenance drift")
    if int(fixture["selector_audit_pr"]) != 188:
        raise AssertionError("selector audit provenance drift")
    if int(fixture["semantic_independence_pr"]) != 189:
        raise AssertionError("semantic-independence provenance drift")
    if fixture["semantic_independence_head_sha"] != "258198c7df7969891a7928f088ec75a90d469282":
        raise AssertionError("#189 head provenance drift")
    if fixture["semantic_independence_merge_sha"] != "2e4cd7b3f170612fe05ad7c334dee504304d8746":
        raise AssertionError("#189 merge provenance drift")

    locked_sources = (
        (SOURCE_SELECTOR_FIXTURE, "source_selector_fixture", "source_selector_fixture_blob_sha"),
        (SOURCE_SELECTOR_MODULE, "source_selector_module", "source_selector_module_blob_sha"),
        (SOURCE_INDEPENDENCE_FIXTURE, "source_independence_fixture", "source_independence_fixture_blob_sha"),
        (SOURCE_INDEPENDENCE_MODULE, "source_independence_module", "source_independence_module_blob_sha"),
    )
    for path, name_key, sha_key in locked_sources:
        if fixture[name_key] != path.name:
            raise AssertionError(f"source path drift: {name_key}")
        if git_blob_sha(path) != fixture[sha_key]:
            raise AssertionError(f"source content drift: {path.name}")

    selector_source_text = SOURCE_SELECTOR_MODULE.read_text(encoding="utf-8")
    if "from post185_fb05_q13_remainder_drift" in selector_source_text or "import post185_fb05_q13_remainder_drift" in selector_source_text:
        raise AssertionError("post-#188 selector target firewall regressed")

    rules = strong_rules(selector_fixture)
    strong_ids = tuple(row["id"] for row in rules)
    strong_fields = tuple(row["field"] for row in rules)
    if strong_ids != EXPECTED_STRONG_IDS:
        raise AssertionError("strong selector id registry drift")
    if strong_fields != EXPECTED_STRONG_FIELDS:
        raise AssertionError("strong selector field registry drift")
    if fixture["strong_selector_ids"] != list(EXPECTED_STRONG_IDS):
        raise AssertionError("fixture strong selector registry drift")
    if not all(bool(row["normalization_invariant"]) for row in rules):
        raise AssertionError("strong selector lost normalization invariance")

    diagnostics = tuple(
        row["id"] for row in selector_fixture["candidate_rules"] if not bool(row["strong_eligible"])
    )
    if diagnostics != EXPECTED_DIAGNOSTIC_IDS:
        raise AssertionError("diagnostic-only selector registry drift")

    forbidden_strong_fields = {
        "remainder_a_component",
        "remainder_b_component",
        "remainder_d_component",
        "mechanism_sum",
        "channel_sum",
        "direct_full_ratio",
        "normalized_domination_margin",
        "chi_scalar_shift",
    }
    if forbidden_strong_fields.intersection(strong_fields):
        raise AssertionError("joint strong vector leaked diagnostic/target information")

    if fixture["required_exact_vector_classification"] != EXACT_VECTOR_CLASSIFICATION:
        raise AssertionError("exact-vector classification policy drift")
    if fixture["required_threshold_signature_classification"] != THRESHOLD_SIGNATURE_CLASSIFICATION:
        raise AssertionError("threshold-signature classification policy drift")
    if fixture["required_target_augmented_classification"] != TARGET_AUGMENTED_CLASSIFICATION:
        raise AssertionError("target-augmented classification policy drift")

    result = audit_fixture(selector_fixture, fixture)
    if result["status"] != "PASS":
        raise AssertionError("joint-selector audit unresolved")
    joint = result["joint_result"]
    if joint["exact_vector_classification"] != EXACT_VECTOR_CLASSIFICATION:
        raise AssertionError("full strong vector not exactly separable")
    if joint["threshold_signature_classification"] != THRESHOLD_SIGNATURE_CLASSIFICATION:
        raise AssertionError("strong threshold signature not separable")
    if not joint["same_exact_strong_vector"]:
        raise AssertionError("strong vector equality failed")
    if not joint["same_nonboundary_threshold_signature"]:
        raise AssertionError("nonboundary threshold signature equality failed")
    if not all(row["residual"] == "0" for row in joint["coordinates"]):
        raise AssertionError("strong-vector coordinate residual nonzero")
    if not joint["smooth_channel_sign_reflection"]:
        raise AssertionError("smooth-channel sign reflection failed")
    if not joint["observed_prime_arch_pole_fixed"]:
        raise AssertionError("observed source-channel coordinates moved")
    if joint["scalar_reflection_residual"] != "0":
        raise AssertionError("scalar-channel reflection residual nonzero")
    if not joint["target_sign_flip"]:
        raise AssertionError("FB-05 normalized target sign did not flip")
    if joint["strong_selector_count"] != 7:
        raise AssertionError("unexpected strong selector count")
    if joint["derived_nonempty_subset_count"] != 127:
        raise AssertionError("unexpected derived subset closure count")
    if not joint["all_nonempty_subsets_closed_by_full_vector_witness"]:
        raise AssertionError("full-vector witness did not close all selector subsets")
    if result["failed_target_augmented_control_ids"]:
        raise AssertionError("target-augmented positive control failed")
    if result["theorem_promotion"] or result["canonical_realizability_claimed"]:
        raise AssertionError("research claim firewall regression")
    if result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("terminal claim firewall regression")

    print(json.dumps({
        "status": "PASS",
        "strong_selector_count": joint["strong_selector_count"],
        "same_exact_strong_vector": joint["same_exact_strong_vector"],
        "same_nonboundary_threshold_signature": joint["same_nonboundary_threshold_signature"],
        "target_sign_flip": joint["target_sign_flip"],
        "smooth_channel_sign_reflection": joint["smooth_channel_sign_reflection"],
        "derived_nonempty_subset_count": joint["derived_nonempty_subset_count"],
        "target_augmented_control_count": len(result["target_augmented_controls"]),
        "canonical_realizability_claimed": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
