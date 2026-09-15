#!/usr/bin/env python3
"""Exact semantic-independence algebra for the post-#188 FB-05 selectors.

The post-#188 selector audit already has a syntactic target firewall.  This
module asks the stronger algebraic question: can one hold an individual frozen
selector on the same side of its predeclared threshold while the normalized
FB-05 domination target changes sign?

The model is deliberately abstract and exact.  It keeps only the normalized
identities used by the selector layer:

    rho = r_a + r_b + r_d
    q   = chi_prime + chi_arch + chi_pole + chi_scalar
    rho = 1 + q
    normalized_domination_margin = 1 - rho = -q

A separating pair is therefore evidence only that a candidate is not an
algebraic restatement of the target inside this normalized identity contract.
It does NOT show that canonical arithmetic CCM states realize the pair.

Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Any


FILTERING_CLASSIFICATION = "ABSTRACTLY_SEPARABLE"
TARGET_EQUIVALENT_CLASSIFICATION = "SEMANTIC_TARGET_EQUIVALENT"


def as_fraction(value: Any) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, str):
        return Fraction(value)
    raise TypeError(f"unsupported exact rational literal: {value!r}")


def threshold_value(kind: str) -> Fraction:
    if kind == "ZERO":
        return Fraction(0, 1)
    if kind == "ONE":
        return Fraction(1, 1)
    raise AssertionError(f"unsupported threshold kind: {kind}")


def sign_name(value: Fraction) -> str:
    if value < 0:
        return "NEGATIVE"
    if value > 0:
        return "POSITIVE"
    return "ZERO"


def relation(value: Fraction, threshold: Fraction) -> str:
    if value < threshold:
        return "LT"
    if value > threshold:
        return "GT"
    return "EQ"


def normalized_state(raw: dict) -> dict[str, Fraction]:
    required = (
        "coupling_ratio",
        "remainder_a_component",
        "remainder_b_component",
        "remainder_d_component",
        "parity_predecessor_ratio",
        "parity_log_slope_gap",
        "chi_prime_signed",
        "chi_arch_signed",
        "chi_pole",
        "chi_scalar_shift",
    )
    missing = [key for key in required if key not in raw]
    if missing:
        raise AssertionError(f"semantic witness missing fields: {missing}")
    return {key: as_fraction(raw[key]) for key in required}


def derived_state(raw: dict) -> dict[str, Fraction]:
    s = normalized_state(raw)
    rho = (
        s["remainder_a_component"]
        + s["remainder_b_component"]
        + s["remainder_d_component"]
    )
    channel_sum = (
        s["chi_prime_signed"]
        + s["chi_arch_signed"]
        + s["chi_pole"]
        + s["chi_scalar_shift"]
    )
    if rho != 1 + channel_sum:
        raise AssertionError(
            "semantic witness violates normalized selector identity rho = 1 + channel_sum"
        )
    smooth = s["chi_arch_signed"] + s["chi_pole"] + s["chi_scalar_shift"]
    target_margin = 1 - rho
    if target_margin != -channel_sum:
        raise AssertionError("normalized domination target reconstruction failed")
    return {
        **s,
        "mechanism_sum": rho,
        "channel_sum": channel_sum,
        "direct_full_ratio": channel_sum,
        "normalized_domination_margin": target_margin,
        "smooth_channel_sum": smooth,
    }


def candidate_value(field: str, state: dict) -> Fraction:
    d = derived_state(state)
    if field == "prime_vs_smooth_sq_ratio":
        smooth = d["smooth_channel_sum"]
        if smooth == 0:
            raise AssertionError("prime-vs-smooth witness has zero smooth channel")
        return d["chi_prime_signed"] ** 2 / smooth ** 2
    if field not in d:
        raise AssertionError(f"unsupported selector field in semantic audit: {field}")
    return d[field]


def filtering_witness_result(rule: dict, witness: dict) -> dict:
    left = derived_state(witness["left"])
    right = derived_state(witness["right"])
    threshold = threshold_value(rule["threshold_kind"])
    left_value = candidate_value(rule["field"], witness["left"])
    right_value = candidate_value(rule["field"], witness["right"])
    left_relation = relation(left_value, threshold)
    right_relation = relation(right_value, threshold)
    left_target = left["normalized_domination_margin"]
    right_target = right["normalized_domination_margin"]

    same_value = left_value == right_value
    same_nonboundary_side = left_relation == right_relation and left_relation in ("LT", "GT")
    target_sign_flip = (
        left_target != 0
        and right_target != 0
        and sign_name(left_target) != sign_name(right_target)
    )
    decisive = same_value and same_nonboundary_side and target_sign_flip
    return {
        "id": rule["id"],
        "field": rule["field"],
        "candidate_class": rule["candidate_class"],
        "strong_eligible": bool(rule["strong_eligible"]),
        "threshold_kind": rule["threshold_kind"],
        "classification": FILTERING_CLASSIFICATION if decisive else "UNRESOLVED",
        "candidate_value": str(left_value),
        "left_relation": left_relation,
        "right_relation": right_relation,
        "left_target_margin": str(left_target),
        "right_target_margin": str(right_target),
        "left_target_sign": sign_name(left_target),
        "right_target_sign": sign_name(right_target),
        "same_candidate_value": same_value,
        "same_nonboundary_threshold_side": same_nonboundary_side,
        "target_sign_flip": target_sign_flip,
        "canonical_realizability_claimed": False,
    }


def target_alias_result(control: dict, states: list[dict]) -> dict:
    field = control["field"]
    kind = control["identity_kind"]
    residuals = []
    target_signs = []
    relations = []
    threshold = threshold_value(control["threshold_kind"])
    for raw in states:
        d = derived_state(raw)
        value = candidate_value(field, raw)
        target = d["normalized_domination_margin"]
        if kind == "ONE_MINUS_VALUE":
            residual = target - (Fraction(1, 1) - value)
        elif kind == "NEGATIVE_VALUE":
            residual = target + value
        else:
            raise AssertionError(f"unsupported target-alias identity: {kind}")
        residuals.append(residual)
        target_signs.append(sign_name(target))
        relations.append(relation(value, threshold))
    exact = all(r == 0 for r in residuals)
    sees_both_target_signs = "POSITIVE" in target_signs and "NEGATIVE" in target_signs
    return {
        "id": control["id"],
        "field": field,
        "identity_kind": kind,
        "classification": (
            TARGET_EQUIVALENT_CLASSIFICATION
            if exact and sees_both_target_signs
            else "UNRESOLVED"
        ),
        "identity_residuals": [str(r) for r in residuals],
        "target_signs": target_signs,
        "threshold_relations": relations,
        "canonical_realizability_claimed": False,
    }


def audit_fixture(selector_fixture: dict, independence_fixture: dict) -> dict:
    rules = {rule["id"]: rule for rule in selector_fixture["candidate_rules"]}
    witness_map = {row["id"]: row for row in independence_fixture["candidate_witnesses"]}
    if set(rules) != set(witness_map):
        raise AssertionError("semantic witness registry must exactly match post-#188 candidate registry")

    candidate_results = [
        filtering_witness_result(rule, witness_map[rid])
        for rid, rule in rules.items()
    ]
    controls = [
        target_alias_result(control, independence_fixture["target_alias_states"])
        for control in independence_fixture["target_alias_controls"]
    ]
    unresolved = [row["id"] for row in candidate_results if row["classification"] == "UNRESOLVED"]
    failed_controls = [
        row["id"] for row in controls
        if row["classification"] != TARGET_EQUIVALENT_CLASSIFICATION
    ]
    return {
        "schema_version": "POST188_FB05_Q14_SELECTOR_SEMANTIC_INDEPENDENCE_RESULT_v1",
        "status": "PASS" if not unresolved and not failed_controls else "UNRESOLVED",
        "candidate_results": candidate_results,
        "target_alias_controls": controls,
        "abstractly_separable_candidate_ids": [
            row["id"] for row in candidate_results
            if row["classification"] == FILTERING_CLASSIFICATION
        ],
        "unresolved_candidate_ids": unresolved,
        "failed_target_alias_control_ids": failed_controls,
        "theorem_promotion": False,
        "canonical_realizability_claimed": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
