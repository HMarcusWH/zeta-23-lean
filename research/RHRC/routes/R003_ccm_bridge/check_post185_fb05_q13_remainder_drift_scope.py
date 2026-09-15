#!/usr/bin/env python3
"""Implementation checks for the post-#185 remainder-drift falsification route."""
from __future__ import annotations

import json
from pathlib import Path

from canonical_source_arb import ball_record, set_precision
from post173_fb05_q13_scalar_barrier import scalar_geometry
from post179_fb05_q13_correlation_preserving_derivative import overlap
from post185_fb05_q13_remainder_drift import (
    interval_remainder_drift_record,
    point_remainder_drift_record,
)
from probe_post185_fb05_q13_remainder_drift_scope import frozen_schedule

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post185_fb05_q13_remainder_drift_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post179_fb05_q13_correlation_preserving_derivative_v1.json"


def _assert_decomposition(label: str, dec: dict, require_h1: bool) -> None:
    if require_h1 and not dec["h1_certified"]:
        raise AssertionError(f"expected exact-center H1 regression: {label}")
    if not dec["h1_certified"]:
        return
    for key in (
        "remainder_direct_residual_overlap",
        "full_decomposition_overlap",
        "ratio_margin_identity_overlap",
        "existing_schur_pivot_derivative_overlap",
    ):
        if not dec.get(key, False):
            raise AssertionError(f"remainder-drift identity regression {key}: {label}")


def _point_box_overlap(label: str, point: dict, interval: dict) -> None:
    p = point["decomposition"]
    q = interval["decomposition"]
    if not (p["h1_certified"] and q["h1_certified"]):
        return
    for field in (
        "envelope_norm_sq",
        "a_remainder_prime",
        "b_remainder_prime",
        "d_remainder_prime",
        "universal_log_drift_L",
        "remainder_envelope_derivative_L",
        "full_pivot_derivative_L",
        "domination_margin_L",
        "normalized_ratio",
    ):
        if not overlap(p[field], q[field]):
            raise AssertionError(f"point/box remainder-drift mismatch {field}: {label}")


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))

    if fixture["theorem_authority_pr"] != 184:
        raise AssertionError("theorem authority regression")
    if fixture["research_anchor_pr"] != 180:
        raise AssertionError("research anchor regression")
    if fixture["routing_sync_pr"] != 185:
        raise AssertionError("routing sync regression")
    if fixture["selected_target"] != source["selected_target"]:
        raise AssertionError("inherited target mismatch")

    norms = scalar_geometry("even")
    if norms.W_norm_sq <= 0 or norms.c_norm_sq <= 0:
        raise AssertionError("nonpositive q13 coordinate norm")

    schedule = frozen_schedule(fixture)
    boxes = schedule["boxes"]
    if schedule["primary_box_count"] != int(fixture["expected_primary_box_count"]):
        raise AssertionError("primary schedule count regression")
    if schedule["control_box_count"] != int(fixture["expected_control_box_count"]):
        raise AssertionError("control schedule count regression")

    set_precision(int(fixture["implementation_check_precision_bits"]))
    records = []
    for box in boxes:
        point = point_remainder_drift_record(box)
        interval = interval_remainder_drift_record(box)
        require_h1 = bool(
            fixture["require_primary_exact_center_h1"]
            and box["primary"]
            and box["role"] == "side"
        )
        _assert_decomposition(box["label"] + ":point", point["decomposition"], require_h1)
        _assert_decomposition(box["label"] + ":box", interval["decomposition"], False)
        _point_box_overlap(box["label"], point, interval)
        records.append({
            "label": box["label"],
            "primary": bool(box["primary"]),
            "role": box["role"],
            "point_h1": bool(point["decomposition"]["h1_certified"]),
            "box_h1": bool(interval["decomposition"]["h1_certified"]),
            "point_L": ball_record(point["base"]["L"]),
            "point_margin_sign": (
                point["decomposition"].get("margin_sign", "OUT_OF_H1_SCOPE")
            ),
            "point_ratio_vs_one": (
                point["decomposition"].get("ratio_vs_one", "OUT_OF_H1_SCOPE")
            ),
        })

    payload = {
        "schema_version": "POST185_FB05_Q13_REMAINDER_DRIFT_CHECK_v1",
        "status": "PASS",
        "claim_cap": "FINITE_REMAINDER_DRIFT_IMPLEMENTATION_CHECK_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "inherited_box_count": len(boxes),
        "coordinate_norms": {
            "W_norm_sq": norms.W_norm_sq,
            "c_norm_sq": norms.c_norm_sq,
        },
        "records": records,
        "checks": {
            "exact_post180_schedule_reconstructed": True,
            "primary_exact_centers_remain_in_H1": True,
            "remainder_coordinates_match_residual_graph": True,
            "full_pivot_matches_universal_plus_remainder": True,
            "ratio_gap_matches_scaled_domination_margin": True,
            "full_pivot_matches_existing_correlation_preserving_schur_graph": True,
            "point_and_box_enclosures_overlap_where_box_H1": True
        },
        "nonclaims": fixture["nonclaims"],
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
