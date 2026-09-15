#!/usr/bin/env python3
"""Exact joint-separability algebra for the post-#189 FB-05 strong selector vector.

PR #189 proved coordinate-by-coordinate semantic separability inside the frozen
normalized selector algebra.  This module asks the strictly stronger joint
question: can *all* strong-eligible post-#188 selector observables remain
exactly fixed, on the same nonboundary sides of their frozen ZERO/ONE
thresholds, while the normalized FB-05 domination target changes sign?

The audit reuses the exact rational algebra from post-#189:

    rho = r_a + r_b + r_d
    q   = chi_prime + chi_arch + chi_pole + chi_scalar
    rho = 1 + q
    normalized_domination_margin = 1 - rho = -q

The decisive witness is a sign reflection of the unobserved smooth channel.
The strong selector C4 sees only its square, so the full seven-dimensional
strong observation vector can stay fixed while the hidden channel sign and the
target sign change.

This is abstract research/audit tooling only.  It does NOT claim canonical
arithmetic CCM realizability.  FB-05 and RH remain OPEN.
"""
from __future__ import annotations

from fractions import Fraction

from post188_fb05_q14_mixed_drift_selector_independence import (
    candidate_value,
    derived_state,
    relation,
    sign_name,
    threshold_value,
)


EXPECTED_STRONG_IDS = (
    "G1_COUPLING_RATIO",
    "P1_PARITY_LEVEL_RATIO",
    "P2_PARITY_LOG_SLOPE_GAP",
    "C1_PRIME_PIVOT_CONTRIBUTION",
    "C2_ARCH_PIVOT_CONTRIBUTION",
    "C3_POLE_PIVOT_CONTRIBUTION",
    "C4_PRIME_VS_SMOOTH_MAGNITUDE",
)

EXACT_VECTOR_CLASSIFICATION = "JOINT_EXACT_VECTOR_SEPARABLE"
THRESHOLD_SIGNATURE_CLASSIFICATION = "JOINT_THRESHOLD_SIGNATURE_SEPARABLE"
TARGET_AUGMENTED_CLASSIFICATION = "TARGET_AUGMENTED_EQUIVALENT"


def strong_rules(selector_fixture: dict) -> list[dict]:
    rules = [row for row in selector_fixture["candidate_rules"] if bool(row["strong_eligible"])]
    ids = tuple(row["id"] for row in rules)
    if ids != EXPECTED_STRONG_IDS:
        raise AssertionError(f"strong selector registry drift: {ids!r}")
    return rules


def _target_sign_flip(left: dict[str, Fraction], right: dict[str, Fraction]) -> bool:
    lt = left["normalized_domination_margin"]
    rt = right["normalized_domination_margin"]
    return lt != 0 and rt != 0 and sign_name(lt) != sign_name(rt)


def joint_witness_result(selector_fixture: dict, witness: dict) -> dict:
    rules = strong_rules(selector_fixture)
    left = derived_state(witness["left"])
    right = derived_state(witness["right"])

    coordinates = []
    exact_vector = True
    same_nonboundary_signature = True
    for rule in rules:
        threshold = threshold_value(rule["threshold_kind"])
        lv = candidate_value(rule["field"], witness["left"])
        rv = candidate_value(rule["field"], witness["right"])
        lr = relation(lv, threshold)
        rr = relation(rv, threshold)
        same_value = lv == rv
        same_side = lr == rr and lr in ("LT", "GT")
        exact_vector = exact_vector and same_value
        same_nonboundary_signature = same_nonboundary_signature and same_side
        coordinates.append({
            "id": rule["id"],
            "field": rule["field"],
            "threshold_kind": rule["threshold_kind"],
            "left_value": str(lv),
            "right_value": str(rv),
            "residual": str(lv - rv),
            "left_relation": lr,
            "right_relation": rr,
            "same_value": same_value,
            "same_nonboundary_threshold_side": same_side,
        })

    smooth_left = left["smooth_channel_sum"]
    smooth_right = right["smooth_channel_sum"]
    smooth_reflection = smooth_left != 0 and smooth_right == -smooth_left

    # The reflection is implemented by changing only the unobserved scalar
    # channel among the four source channels.  Prime/arch/pole remain fixed.
    observed_channels_fixed = all(
        left[field] == right[field]
        for field in ("chi_prime_signed", "chi_arch_signed", "chi_pole")
    )
    expected_right_scalar = (
        -2 * (left["chi_arch_signed"] + left["chi_pole"])
        - left["chi_scalar_shift"]
    )
    scalar_reflection_residual = right["chi_scalar_shift"] - expected_right_scalar

    target_flip = _target_sign_flip(left, right)
    threshold_decisive = same_nonboundary_signature and target_flip
    exact_decisive = exact_vector and threshold_decisive
    symmetry_decisive = (
        exact_decisive
        and smooth_reflection
        and observed_channels_fixed
        and scalar_reflection_residual == 0
    )

    return {
        "exact_vector_classification": (
            EXACT_VECTOR_CLASSIFICATION if symmetry_decisive else "UNRESOLVED"
        ),
        "threshold_signature_classification": (
            THRESHOLD_SIGNATURE_CLASSIFICATION if threshold_decisive else "UNRESOLVED"
        ),
        "strong_selector_ids": list(EXPECTED_STRONG_IDS),
        "strong_selector_count": len(EXPECTED_STRONG_IDS),
        "derived_nonempty_subset_count": (1 << len(EXPECTED_STRONG_IDS)) - 1,
        "coordinates": coordinates,
        "same_exact_strong_vector": exact_vector,
        "same_nonboundary_threshold_signature": same_nonboundary_signature,
        "left_threshold_signature": [row["left_relation"] for row in coordinates],
        "right_threshold_signature": [row["right_relation"] for row in coordinates],
        "left_smooth_channel": str(smooth_left),
        "right_smooth_channel": str(smooth_right),
        "smooth_channel_sign_reflection": smooth_reflection,
        "observed_prime_arch_pole_fixed": observed_channels_fixed,
        "scalar_reflection_residual": str(scalar_reflection_residual),
        "left_channel_sum": str(left["channel_sum"]),
        "right_channel_sum": str(right["channel_sum"]),
        "left_mechanism_sum": str(left["mechanism_sum"]),
        "right_mechanism_sum": str(right["mechanism_sum"]),
        "left_target_margin": str(left["normalized_domination_margin"]),
        "right_target_margin": str(right["normalized_domination_margin"]),
        "left_target_sign": sign_name(left["normalized_domination_margin"]),
        "right_target_sign": sign_name(right["normalized_domination_margin"]),
        "target_sign_flip": target_flip,
        "all_nonempty_subsets_closed_by_full_vector_witness": symmetry_decisive,
        "canonical_realizability_claimed": False,
    }


def target_augmented_control_result(
    selector_fixture: dict, witness: dict, control: dict
) -> dict:
    joint = joint_witness_result(selector_fixture, witness)
    left = derived_state(witness["left"])
    right = derived_state(witness["right"])
    field = control["field"]
    kind = control["identity_kind"]
    lv = left[field]
    rv = right[field]
    lt = left["normalized_domination_margin"]
    rt = right["normalized_domination_margin"]

    if kind == "NEGATIVE_VALUE":
        residuals = (lt + lv, rt + rv)
    elif kind == "ONE_MINUS_VALUE":
        residuals = (lt - (1 - lv), rt - (1 - rv))
    else:
        raise AssertionError(f"unsupported target-augmented identity: {kind}")

    exact_identity = all(r == 0 for r in residuals)
    alias_distinguishes = lv != rv
    decisive = (
        joint["same_exact_strong_vector"]
        and joint["target_sign_flip"]
        and exact_identity
        and alias_distinguishes
    )
    return {
        "id": control["id"],
        "field": field,
        "identity_kind": kind,
        "classification": TARGET_AUGMENTED_CLASSIFICATION if decisive else "UNRESOLVED",
        "left_value": str(lv),
        "right_value": str(rv),
        "values_differ": alias_distinguishes,
        "identity_residuals": [str(r) for r in residuals],
        "target_sign_flip": joint["target_sign_flip"],
        "canonical_realizability_claimed": False,
    }


def audit_fixture(selector_fixture: dict, fixture: dict) -> dict:
    joint = joint_witness_result(selector_fixture, fixture["joint_witness"])
    controls = [
        target_augmented_control_result(selector_fixture, fixture["joint_witness"], control)
        for control in fixture["target_augmented_controls"]
    ]
    failed_controls = [
        row["id"] for row in controls
        if row["classification"] != TARGET_AUGMENTED_CLASSIFICATION
    ]
    passed = (
        joint["exact_vector_classification"] == EXACT_VECTOR_CLASSIFICATION
        and joint["threshold_signature_classification"] == THRESHOLD_SIGNATURE_CLASSIFICATION
        and not failed_controls
    )
    return {
        "schema_version": "POST189_FB05_JOINT_SELECTOR_SEPARABILITY_RESULT_v1",
        "status": "PASS" if passed else "UNRESOLVED",
        "joint_result": joint,
        "target_augmented_controls": controls,
        "failed_target_augmented_control_ids": failed_controls,
        "theorem_promotion": False,
        "canonical_realizability_claimed": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
