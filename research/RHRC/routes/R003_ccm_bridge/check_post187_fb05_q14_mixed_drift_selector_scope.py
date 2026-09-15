#!/usr/bin/env python3
"""Implementation and leakage checks for the post-#187 selector audit."""
from __future__ import annotations

import json
from pathlib import Path

from canonical_source_arb import set_precision
from post179_fb05_q13_correlation_preserving_derivative import overlap
from post185_fb05_q13_remainder_drift import point_remainder_drift_record
from post187_fb05_q14_mixed_drift_selector import (
    normalization_invariance_record,
    selector_record_from_box,
)
from probe_post185_fb05_q13_remainder_drift_scope import frozen_schedule

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post185_fb05_q13_remainder_drift_v1.json"

EXPECTED_RULES = {
    "G1_COUPLING_RATIO": ("coupling_ratio", "ONE", "INDEPENDENT_GEOMETRY", True),
    "R1_PREDECESSOR_REMAINDER_COMPONENT": ("remainder_a_component", "ZERO", "MECHANISM_DIAGNOSTIC", False),
    "R2_CROSS_REMAINDER_COMPONENT": ("remainder_b_component", "ZERO", "MECHANISM_DIAGNOSTIC", False),
    "R3_SHELL_REMAINDER_COMPONENT": ("remainder_d_component", "ZERO", "MECHANISM_DIAGNOSTIC", False),
    "P1_PARITY_LEVEL_RATIO": ("parity_predecessor_ratio", "ONE", "PARITY", True),
    "P2_PARITY_LOG_SLOPE_GAP": ("parity_log_slope_gap", "ZERO", "PARITY", True),
    "C1_PRIME_PIVOT_CONTRIBUTION": ("chi_prime_signed", "ZERO", "SOURCE_CHANNEL", True),
    "C2_ARCH_PIVOT_CONTRIBUTION": ("chi_arch_signed", "ZERO", "SOURCE_CHANNEL", True),
    "C3_POLE_PIVOT_CONTRIBUTION": ("chi_pole", "ZERO", "SOURCE_CHANNEL", True),
    "C4_PRIME_VS_SMOOTH_MAGNITUDE": ("prime_vs_smooth_sq_ratio", "ONE", "SOURCE_CHANNEL", True),
}


def _validate_fixture(fixture: dict, source: dict) -> None:
    if fixture["source_fixture"] != SOURCE_FIXTURE.name:
        raise AssertionError("selector source fixture drift")
    if fixture["selected_target"] != source["selected_target"]:
        raise AssertionError("selector target drift")
    if fixture["required_ancestry_control"] != source["required_ancestry_control"]:
        raise AssertionError("selector ancestry drift")
    if int(fixture["expected_primary_box_count"]) != int(source["expected_primary_box_count"]):
        raise AssertionError("selector primary count drift")
    if int(fixture["expected_control_box_count"]) != int(source["expected_control_box_count"]):
        raise AssertionError("selector control count drift")
    if fixture["orientation_policy"] != "PRIMARY_DISCOVERY_ONLY":
        raise AssertionError("holdouts must not select candidate orientation")

    rules = fixture["candidate_rules"]
    if len(rules) != len(EXPECTED_RULES):
        raise AssertionError("candidate registry size drift")
    forbidden = set(fixture["forbidden_selector_fields"])
    seen = set()
    for rule in rules:
        rid = rule["id"]
        if rid in seen or rid not in EXPECTED_RULES:
            raise AssertionError(f"unknown/duplicate candidate rule: {rid}")
        seen.add(rid)
        expected = EXPECTED_RULES[rid]
        actual = (
            rule["field"], rule["threshold_kind"], rule["candidate_class"],
            bool(rule["strong_eligible"]),
        )
        if actual != expected:
            raise AssertionError(f"candidate rule drift: {rid}")
        if rule["threshold_kind"] not in ("ZERO", "ONE"):
            raise AssertionError(f"fitted/arbitrary threshold forbidden: {rid}")
        if rule["field"] in forbidden:
            raise AssertionError(f"target-leaking selector field: {rule['field']}")
        if not bool(rule["normalization_invariant"]):
            raise AssertionError(f"all registered candidates must be normalization invariant: {rid}")

    for scale in fixture["normalization_rescalings"]:
        for key in ("even_predecessor", "shell", "odd_predecessor"):
            if int(scale[key]) == 0:
                raise AssertionError("zero basis rescaling is invalid")


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))
    _validate_fixture(fixture, source)
    set_precision(int(fixture["implementation_check_precision_bits"]))

    schedule = frozen_schedule(source)
    boxes = schedule["boxes"]
    if sum(1 for b in boxes if b["primary"]) != int(fixture["expected_primary_box_count"]):
        raise AssertionError("inherited primary schedule regression")
    if sum(1 for b in boxes if not b["primary"]) != int(fixture["expected_control_box_count"]):
        raise AssertionError("inherited control schedule regression")

    candidate_fields = {rule["field"] for rule in fixture["candidate_rules"]}
    checked_primary = 0
    checked_h1 = 0
    for box in boxes:
        rec = selector_record_from_box(box)
        target = point_remainder_drift_record(box)["decomposition"]
        if box["primary"] and box["role"] == "side":
            checked_primary += 1
            if rec["scope"] != "CERTIFIED_H1_SCOPE":
                raise AssertionError(f"primary exact-center selector H1 regression: {box['label']}")
        if rec["scope"] != "CERTIFIED_H1_SCOPE":
            continue
        checked_h1 += 1
        if set(rec["candidates"]) != candidate_fields:
            raise AssertionError(f"candidate field registry mismatch: {box['label']}")
        for key in ("channel_matrix_reconstruction_overlap", "channel_directional_sum_overlap"):
            if not rec["checks"].get(key, False):
                raise AssertionError(f"selector implementation check failed {key}: {box['label']}")

        inv = normalization_invariance_record(box, fixture["normalization_rescalings"])
        if not inv["all_overlap"]:
            raise AssertionError(f"normalization/sign-flip invariance failed: {box['label']}")

        if target["h1_certified"]:
            rho = target["normalized_ratio"]
            if not overlap(rec["diagnostics"]["mechanism_sum"], rho):
                raise AssertionError(f"remainder-component sum does not recover rho: {box['label']}")
            if not overlap(arb_one_plus(rec["diagnostics"]["channel_sum"]), rho):
                raise AssertionError(f"four-way channel sum does not recover rho-1: {box['label']}")

    if checked_primary != int(fixture["expected_primary_box_count"]):
        raise AssertionError("primary selector check count mismatch")
    if checked_h1 < checked_primary:
        raise AssertionError("unexpected loss of all H1 controls")

    print(json.dumps({
        "status": "PASS",
        "primary_count": checked_primary,
        "h1_record_count": checked_h1,
        "candidate_rule_count": len(fixture["candidate_rules"]),
        "target_import_confined_to_checker": True,
        "normalization_sign_flip_checks": "PASS"
    }, indent=2))
    return 0


def arb_one_plus(x):
    from flint import arb
    return arb(1) + x


if __name__ == "__main__":
    raise SystemExit(main())
