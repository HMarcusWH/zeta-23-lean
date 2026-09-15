#!/usr/bin/env python3
"""Certify exact joint separability of the post-#189 strong selector vector.

Green means the frozen seven-dimensional strong observation vector is exactly
identical on two exact rational states, its entire ZERO/ONE threshold signature
is identical and nonboundary, and the normalized FB-05 target sign nevertheless
flips.  The certificate also verifies that appending deliberate target aliases
restores target information.

No canonical arithmetic realizability is claimed.  RH remains OPEN.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post189_fb05_joint_selector_separability import (
    EXACT_VECTOR_CLASSIFICATION,
    TARGET_AUGMENTED_CLASSIFICATION,
    THRESHOLD_SIGNATURE_CLASSIFICATION,
    audit_fixture,
)
from probe_post189_fb05_joint_selector_separability_scope import joint_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post189_fb05_joint_selector_separability_v1.json"
SOURCE_SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"


def _validate_schedule(fixture: dict, selector_fixture: dict, schedule: dict) -> None:
    expected = joint_schedule(fixture, selector_fixture)
    keys = (
        "schema_version",
        "status",
        "claim_cap",
        "base_main_sha",
        "theorem_authority_pr",
        "mixed_drift_falsification_pr",
        "selector_audit_pr",
        "semantic_independence_pr",
        "semantic_independence_head_sha",
        "semantic_independence_merge_sha",
        "source_selector_fixture_schema_version",
        "strong_selector_ids",
        "joint_witness",
        "target_augmented_controls",
        "canonical_production_labels_included",
        "grid_search_permitted",
        "threshold_refitting_permitted",
        "new_selector_features_permitted",
        "canonical_realizability_claimed",
    )
    for key in keys:
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"joint-selector schedule drift: {key}")
    if schedule["canonical_production_labels_included"] is not False:
        raise AssertionError("joint audit leaked canonical production labels")
    if schedule["grid_search_permitted"] is not False:
        raise AssertionError("joint audit permitted post-hoc grid search")
    if schedule["threshold_refitting_permitted"] is not False:
        raise AssertionError("joint audit permitted threshold refitting")
    if schedule["new_selector_features_permitted"] is not False:
        raise AssertionError("joint audit permitted new selector features")
    if schedule["canonical_realizability_claimed"] is not False:
        raise AssertionError("joint audit overclaimed canonical realizability")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST189_FB05_JOINT_SELECTOR_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SOURCE_SELECTOR_FIXTURE.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, selector_fixture, schedule)

    result = audit_fixture(selector_fixture, fixture)
    if result["status"] != "PASS":
        raise AssertionError("joint-selector certification unresolved")
    joint = result["joint_result"]
    if joint["exact_vector_classification"] != EXACT_VECTOR_CLASSIFICATION:
        raise AssertionError("joint exact-vector separability failed")
    if joint["threshold_signature_classification"] != THRESHOLD_SIGNATURE_CLASSIFICATION:
        raise AssertionError("joint threshold-signature separability failed")
    if not joint["same_exact_strong_vector"]:
        raise AssertionError("full strong vector changed across witness pair")
    if not joint["same_nonboundary_threshold_signature"]:
        raise AssertionError("frozen threshold signature changed or touched a boundary")
    if joint["left_threshold_signature"] != joint["right_threshold_signature"]:
        raise AssertionError("threshold signature residual")
    if any(rel not in ("LT", "GT") for rel in joint["left_threshold_signature"]):
        raise AssertionError("threshold signature contains a boundary equality")
    for row in joint["coordinates"]:
        if row["residual"] != "0" or not row["same_value"]:
            raise AssertionError(f"strong selector moved: {row['id']}")
        if not row["same_nonboundary_threshold_side"]:
            raise AssertionError(f"strong selector threshold side changed: {row['id']}")
    if not joint["smooth_channel_sign_reflection"]:
        raise AssertionError("smooth-channel sign reflection not exact")
    if joint["scalar_reflection_residual"] != "0":
        raise AssertionError("scalar reflection identity residual nonzero")
    if not joint["observed_prime_arch_pole_fixed"]:
        raise AssertionError("observed prime/arch/pole channel changed")
    if not joint["target_sign_flip"]:
        raise AssertionError("normalized FB-05 target sign did not flip")
    if joint["left_target_sign"] == "ZERO" or joint["right_target_sign"] == "ZERO":
        raise AssertionError("target witness touched zero")
    if joint["left_target_sign"] == joint["right_target_sign"]:
        raise AssertionError("target signs agree")
    if joint["strong_selector_count"] != 7:
        raise AssertionError("strong selector count drift")
    if joint["derived_nonempty_subset_count"] != 127:
        raise AssertionError("derived subset count drift")
    if not joint["all_nonempty_subsets_closed_by_full_vector_witness"]:
        raise AssertionError("full-vector witness failed to close all nonempty subsets")

    for row in result["target_augmented_controls"]:
        if row["classification"] != TARGET_AUGMENTED_CLASSIFICATION:
            raise AssertionError(f"target-augmented positive control failed: {row['id']}")
        if not row["values_differ"]:
            raise AssertionError(f"target alias failed to distinguish pair: {row['id']}")
        if any(residual != "0" for residual in row["identity_residuals"]):
            raise AssertionError(f"target-alias identity residual nonzero: {row['id']}")
        if not row["target_sign_flip"]:
            raise AssertionError(f"target-alias control lost target flip: {row['id']}")

    if result["theorem_promotion"] or result["canonical_realizability_claimed"]:
        raise AssertionError("research claim firewall regression")
    if result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("terminal claim firewall regression")

    out = {
        "schema_version": "POST189_FB05_JOINT_SELECTOR_SEPARABILITY_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "provenance": {
            "base_main_sha": fixture["base_main_sha"],
            "theorem_authority_pr": fixture["theorem_authority_pr"],
            "mixed_drift_falsification_pr": fixture["mixed_drift_falsification_pr"],
            "selector_audit_pr": fixture["selector_audit_pr"],
            "semantic_independence_pr": fixture["semantic_independence_pr"],
            "semantic_independence_head_sha": fixture["semantic_independence_head_sha"],
            "semantic_independence_merge_sha": fixture["semantic_independence_merge_sha"],
        },
        "result": result,
        "derived_closure": {
            "strong_selector_count": joint["strong_selector_count"],
            "nonempty_selector_subset_count": joint["derived_nonempty_subset_count"],
            "all_nonempty_subsets_share_the_same_countermodel": True,
            "interpretation": "Because the entire frozen strong-selector vector is identical across the witness pair while the target sign flips, no deterministic function of any subset of those seven observables can universally determine the target sign in the audited abstract algebra."
        },
        "interpretation": {
            "joint_result": "The full seven-dimensional strong post-#188 selector vector and its complete nonboundary threshold signature are exactly blind to an FB-05 target-sign flip in the frozen post-#189 normalized algebra.",
            "symmetry_result": "A scalar-channel reflection flips the hidden smooth-channel sign while preserving the squared prime-vs-smooth observable and all other strong coordinates.",
            "positive_control_result": "Appending channel_sum, mechanism_sum, or direct_full_ratio restores exact target information and distinguishes the witness pair.",
            "next_question": "Which additional canonical arithmetic CCM realizability constraint forbids one member of this reflected abstract pair remains open."
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
        "strong_selector_count": joint["strong_selector_count"],
        "same_exact_strong_vector": True,
        "same_nonboundary_threshold_signature": True,
        "target_sign_flip": True,
        "derived_nonempty_subset_count": joint["derived_nonempty_subset_count"],
        "target_augmented_control_count": len(result["target_augmented_controls"]),
        "canonical_realizability_claimed": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
