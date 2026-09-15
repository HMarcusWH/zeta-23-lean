#!/usr/bin/env python3
"""Implementation checks for the post-#179 correlation-preserving derivative route."""
from __future__ import annotations

import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post166_fb05_cell_interval import (
    _arb_matrix_from_sympy,
    cell_coordinate_L_arb,
    fixed_q_canonical_source_matrix_arb,
)
from post169_fb05_schur_visibility import one_step_geometry
from probe_post177_fb05_q13_fixed_unit_derivative_scope import expected_boxes
from post179_fb05_q13_correlation_preserving_derivative import (
    interval_record_from_box,
    overlap,
    point_record_from_box,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post179_fb05_q13_correlation_preserving_derivative_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def _direct_delta2(Q: int, L: arb, successor_K: int) -> arb:
    M = fixed_q_canonical_source_matrix_arb(L, successor_K, Q)
    geom = one_step_geometry(successor_K - 1, "even")
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * M * B
    if H.nrows() != 2 or H.ncols() != 2:
        raise AssertionError("unexpected direct-value restriction dimension")
    return H[0, 0] * H[1, 1] - H[0, 1] * H[0, 1]


def _agreement_record(analytic: arb, finite_difference: arb, atol: float, rtol: float) -> dict:
    err = abs(analytic - finite_difference)
    tol = arb(str(atol)) + arb(str(rtol)) * (arb(1) + abs(analytic))
    return {
        "analytic": ball_record(analytic),
        "finite_difference": ball_record(finite_difference),
        "error": ball_record(err),
        "tolerance": ball_record(tol),
        "ok": bool(err < tol),
    }


def _check_point(box: dict, fixture: dict) -> dict:
    point = point_record_from_box(box)
    even = point["record"]["even"]
    schur = point["schur"]

    if schur["h1_certified"]:
        if not schur["delta2_overlap"]:
            raise AssertionError(f"point delta factorization mismatch: {box['label']}")
        if not schur["delta2_prime_overlap"]:
            raise AssertionError(f"point derivative factorization mismatch: {box['label']}")
        if not schur["pivot_prime_overlap"]:
            raise AssertionError(f"point pivot derivative mismatch: {box['label']}")

    atol = float(fixture["finite_difference_absolute_tolerance"])
    rtol = float(fixture["finite_difference_relative_tolerance"])
    K = int(fixture["selected_target"]["successor_K"])
    ladder = []
    for h_bit in fixture["finite_difference_h_bits"]:
        h_bit = int(h_bit)
        h = arb(1) / (1 << h_bit)
        dp = _direct_delta2(int(box["Q"]), point["L"] + h, K)
        dm = _direct_delta2(int(box["Q"]), point["L"] - h, K)
        fd = (dp - dm) / (2 * h)
        raw_cmp = _agreement_record(even["delta2_prime"], fd, atol, rtol)
        if not raw_cmp["ok"]:
            raise AssertionError(f"direct-value finite-difference mismatch: {box['label']} h=2^-{h_bit}")
        row = {"h_bit": h_bit, "raw": raw_cmp}
        if schur["h1_certified"]:
            schur_cmp = _agreement_record(schur["delta2_prime_factorized"], fd, atol, rtol)
            if not schur_cmp["ok"]:
                raise AssertionError(f"Schur finite-difference mismatch: {box['label']} h=2^-{h_bit}")
            row["schur"] = schur_cmp
        ladder.append(row)

    return {
        "label": box["label"],
        "Q": int(box["Q"]),
        "center_num": int(box["center_num"]),
        "den": int(box["den"]),
        "L": ball_record(point["L"]),
        "h1_certified": bool(schur["h1_certified"]),
        "finite_difference_ladder": ladder,
    }


def _check_box(box: dict) -> dict:
    point = point_record_from_box(box)
    interval = interval_record_from_box(box)
    if not overlap(point["raw_delta2_prime"], interval["raw_delta2_prime"]):
        raise AssertionError(f"point/raw-box derivative mismatch: {box['label']}")

    schur_point = point["schur"]
    schur_box = interval["schur"]
    if schur_box["h1_certified"]:
        if not schur_box["delta2_overlap"]:
            raise AssertionError(f"box delta factorization mismatch: {box['label']}")
        if not schur_box["delta2_prime_overlap"]:
            raise AssertionError(f"box derivative factorization mismatch: {box['label']}")
        if not schur_box["pivot_prime_overlap"]:
            raise AssertionError(f"box pivot derivative mismatch: {box['label']}")
    if schur_point["h1_certified"] and schur_box["h1_certified"]:
        if not overlap(
            schur_point["delta2_prime_factorized"],
            schur_box["delta2_prime_factorized"],
        ):
            raise AssertionError(f"point/Schur-box derivative mismatch: {box['label']}")

    return {
        "label": box["label"],
        "point_h1": bool(schur_point["h1_certified"]),
        "box_h1": bool(schur_box["h1_certified"]),
        "raw_point_box_overlap": True,
        "schur_point_box_overlap": bool(
            not (schur_point["h1_certified"] and schur_box["h1_certified"])
            or overlap(
                schur_point["delta2_prime_factorized"],
                schur_box["delta2_prime_factorized"],
            )
        ),
    }


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))

    if fixture["theorem_authority_pr"] != 163:
        raise AssertionError("theorem authority regression")
    if fixture["research_anchor_pr"] != 178 or fixture["routing_sync_pr"] != 179:
        raise AssertionError("post-#179 authority regression")
    if fixture["selected_target"] != source["selected_target"]:
        raise AssertionError("inherited target mismatch")

    boxes = expected_boxes(source)
    primary_count = sum(1 for b in boxes if b["primary"])
    control_count = len(boxes) - primary_count
    if primary_count != int(fixture["expected_primary_box_count"]):
        raise AssertionError("primary schedule count regression")
    if control_count != int(fixture["expected_control_box_count"]):
        raise AssertionError("control schedule count regression")

    set_precision(int(fixture["implementation_check_precision_bits"]))
    point_checks = [_check_point(box, fixture) for box in boxes]
    box_checks = [_check_box(box) for box in boxes]

    payload = {
        "schema_version": "POST179_FB05_Q13_CORRELATION_PRESERVING_DERIVATIVE_CHECK_v1",
        "status": "PASS",
        "claim_cap": "FINITE_CORRELATION_DERIVATIVE_IMPLEMENTATION_CHECK_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "inherited_box_count": len(boxes),
        "point_checks": point_checks,
        "box_checks": box_checks,
        "checks": {
            "exact_post177_schedule_reconstructed": True,
            "raw_and_schur_determinants_overlap_in_certified_h1": True,
            "raw_and_schur_derivatives_overlap_in_certified_h1": True,
            "directional_and_quotient_pivot_derivatives_overlap": True,
            "exact_center_derivatives_match_independent_direct_value_finite_differences": True,
            "point_and_box_enclosures_overlap": True
        },
        "nonclaims": fixture["nonclaims"],
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
