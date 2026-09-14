#!/usr/bin/env python3
"""Deterministic implementation checks for the post-#177 derivative route."""
from __future__ import annotations

import copy
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import alpha_L, ball_record, beta_L, set_precision, source_eq44_gamma_L
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post175_fb05_q13_fixed_unit_enclosure import (
    fixed_unit_alpha_L,
    fixed_unit_beta_L,
    fixed_unit_fixed_q_canonical_source_matrix_arb,
    fixed_unit_scalar_record_arb_at_L,
    fixed_unit_source_eq44_gamma_L,
)
from certify_post175_fb05_q13_fixed_unit_enclosure_scope import (
    expected_benchmark_boxes,
    validate_benchmark_schedule,
)
from post177_fb05_q13_fixed_unit_derivative import (
    derivative_seam_overlap_record,
    fixed_unit_alpha_L_prime,
    fixed_unit_beta_L_prime,
    fixed_unit_derivative_scalar_record_arb_at_L,
    fixed_unit_source_eq44_gamma_L_prime,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"
POST175_FIXTURE = HERE / "fixtures" / "post175_fb05_q13_fixed_unit_enclosure_v1.json"


def _quantized_t(value: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(value) * den))
    num = max(1, min(den - 1, num))
    return num, den


def _fd_scalar(func, L: arb, h: arb) -> arb:
    return (func(L + h) - func(L - h)) / (2 * h)


def _agreement_record(analytic: arb, finite_difference: arb, atol: float, rtol: float) -> dict:
    err = abs(analytic - finite_difference)
    tol = arb(str(atol)) + arb(str(rtol)) * (arb(1) + abs(analytic))
    ok = bool(err < tol)
    return {
        "analytic": ball_record(analytic),
        "finite_difference": ball_record(finite_difference),
        "error": ball_record(err),
        "tolerance": ball_record(tol),
        "ok": ok,
    }


def _assert_record_ok(rec: dict, context: str) -> None:
    if not rec["ok"]:
        raise AssertionError(f"derivative finite-difference mismatch: {context}")


def _post175_schedule_hardening_checks() -> dict:
    fixture = json.loads(POST175_FIXTURE.read_text(encoding="utf-8"))
    boxes = expected_benchmark_boxes(fixture)
    base = {
        "schema_version": "POST175_FB05_Q13_FIXED_UNIT_BENCHMARK_v1",
        "status": "PASS",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "boxes": copy.deepcopy(boxes),
        "primary_box_count": sum(1 for b in boxes if b["primary"]),
        "control_box_count": sum(1 for b in boxes if not b["primary"]),
    }
    validate_benchmark_schedule(fixture, base)

    mutations: dict[str, dict] = {}

    x = copy.deepcopy(base)
    x["boxes"].pop(0)
    x["primary_box_count"] -= 1
    mutations["missing_primary"] = x

    x = copy.deepcopy(base)
    x["boxes"][0]["den"] *= 2
    mutations["wrong_denominator"] = x

    x = copy.deepcopy(base)
    x["boxes"][0]["label"] = "relabeled_primary"
    mutations["wrong_label"] = x

    x = copy.deepcopy(base)
    x["boxes"].append(copy.deepcopy(x["boxes"][0]))
    x["primary_box_count"] += 1
    mutations["duplicate_box"] = x

    x = copy.deepcopy(base)
    extra = copy.deepcopy(x["boxes"][-1])
    extra["label"] = "unexpected_extra"
    x["boxes"].append(extra)
    x["control_box_count"] += 1
    mutations["extra_box"] = x

    rejected = {}
    for name, payload in mutations.items():
        try:
            validate_benchmark_schedule(fixture, payload)
        except AssertionError:
            rejected[name] = True
        else:
            rejected[name] = False
            raise AssertionError(f"post-#175 replay hardening failed to reject {name}")
    return {"canonical_schedule_passes": True, "mutations_rejected": rejected}


def _point_check(point: dict, fixture: dict) -> dict:
    bits = int(fixture["point_quantization_bits"])
    num, den = _quantized_t(float(point["t"]), bits)
    t = arb(num) / den
    Q = int(point["Q"])
    L = cell_coordinate_L_arb(Q, t)
    rtol = float(fixture["finite_difference_relative_tolerance"])
    atol = float(fixture["finite_difference_absolute_tolerance"])
    h_bits = [int(x) for x in fixture["finite_difference_h_bits"]]
    n_values = [int(x) for x in fixture["derivative_check_n_values"]]

    analytic = fixed_unit_derivative_scalar_record_arb_at_L(Q, L)
    primitive_rows = []
    value_funcs = {
        "alpha": (fixed_unit_alpha_L, alpha_L, fixed_unit_alpha_L_prime),
        "beta": (fixed_unit_beta_L, beta_L, fixed_unit_beta_L_prime),
        "gamma": (fixed_unit_source_eq44_gamma_L, source_eq44_gamma_L, fixed_unit_source_eq44_gamma_L_prime),
    }
    for n in n_values:
        row = {"n": n}
        for name, (fixed_value, direct_value, deriv_func) in value_funcs.items():
            a = deriv_func(n, L)
            ladder = []
            for hb in h_bits:
                h = arb(1) / (1 << hb)
                fd = _fd_scalar(lambda x, f=fixed_value, nn=n: f(nn, x), L, h)
                rec = _agreement_record(a, fd, atol, rtol)
                ladder.append({"h_bit": hb, **rec})
            _assert_record_ok(ladder[-1], f"{point['label']} {name} n={n} fixed-unit")

            h = arb(1) / (1 << h_bits[-1])
            direct_fd = _fd_scalar(lambda x, f=direct_value, nn=n: f(nn, x), L, h)
            direct_rec = _agreement_record(a, direct_fd, atol, rtol)
            _assert_record_ok(direct_rec, f"{point['label']} {name} n={n} direct")
            row[name] = {"fixed_unit_ladder": ladder, "direct_final": direct_rec}
        primitive_rows.append(row)

    # Complete-matrix finite difference uses the already-green fixed-unit value
    # evaluator and checks every 7x7 entry independently of the derivative code.
    h = arb(1) / (1 << h_bits[-1])
    Mp = fixed_unit_fixed_q_canonical_source_matrix_arb(L + h, 3, Q)
    Mm = fixed_unit_fixed_q_canonical_source_matrix_arb(L - h, 3, Q)
    matrix_checks = []
    for r in range(analytic["matrix_prime"].nrows()):
        for c in range(r, analytic["matrix_prime"].ncols()):
            fd = (Mp[r, c] - Mm[r, c]) / (2 * h)
            rec = _agreement_record(analytic["matrix_prime"][r, c], fd, atol, rtol)
            _assert_record_ok(rec, f"{point['label']} M'[{r},{c}]")
            matrix_checks.append({"r": r, "c": c, **rec})

    # Check theorem-aligned scalar derivatives from finite differences of the
    # pre-existing value-level scalar evaluator.  Delta_2' is assembled from
    # independently differenced a,b,d to avoid a near-minimum subtraction test.
    sp = fixed_unit_scalar_record_arb_at_L(Q, L + h)
    sm = fixed_unit_scalar_record_arb_at_L(Q, L - h)
    sc = fixed_unit_scalar_record_arb_at_L(Q, L)
    ap_fd = (sp["even"]["a"] - sm["even"]["a"]) / (2 * h)
    bp_fd = (sp["even"]["b"] - sm["even"]["b"]) / (2 * h)
    dp_fd = (sp["even"]["d"] - sm["even"]["d"]) / (2 * h)
    delta_fd = ap_fd * sc["even"]["d"] + sc["even"]["a"] * dp_fd - 2 * sc["even"]["b"] * bp_fd
    odd_fd = (sp["odd_N2_predecessor"] - sm["odd_N2_predecessor"]) / (2 * h)
    scalar_pairs = {
        "a_prime": (analytic["even"]["a_prime"], ap_fd),
        "b_prime": (analytic["even"]["b_prime"], bp_fd),
        "d_prime": (analytic["even"]["d_prime"], dp_fd),
        "delta2_prime": (analytic["even"]["delta2_prime"], delta_fd),
        "odd_N2_predecessor_prime": (analytic["odd_N2_predecessor_prime"], odd_fd),
    }
    scalar_checks = {}
    for name, (a, fd) in scalar_pairs.items():
        rec = _agreement_record(a, fd, atol, rtol)
        _assert_record_ok(rec, f"{point['label']} {name}")
        scalar_checks[name] = rec

    return {
        "label": point["label"],
        "Q": Q,
        "t_num": num,
        "t_den": den,
        "L": ball_record(L),
        "primitive_derivative_checks": primitive_rows,
        "matrix_prime_upper_triangle_checks": matrix_checks,
        "scalar_derivative_checks": scalar_checks,
    }


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture["selected_target"] != {
        "q_start": 13,
        "q_end": 16,
        "predecessor_N": 2,
        "successor_K": 3,
        "selected_parity": "even",
        "primary_Q": 14,
    }:
        raise AssertionError("post-#177 derivative target regression")

    hardening = _post175_schedule_hardening_checks()
    set_precision(int(fixture["implementation_check_precision_bits"]))
    point_checks = [_point_check(p, fixture) for p in fixture["derivative_check_points"]]
    seam_checks = [derivative_seam_overlap_record(int(k)) for k in fixture["required_derivative_zero_weight_seams"]]
    if not all(r["all_overlap"] for r in seam_checks):
        raise AssertionError("zero-weight derivative seam regression")

    payload = {
        "schema_version": "POST177_FB05_Q13_FIXED_UNIT_DERIVATIVE_CHECK_v1",
        "status": "PASS",
        "claim_cap": "FINITE_DERIVATIVE_IMPLEMENTATION_CHECK_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "post175_replay_hardening": hardening,
        "point_checks": point_checks,
        "zero_weight_derivative_seams": seam_checks,
        "checks": {
            "post175_schedule_mutations_rejected": True,
            "fixed_unit_analytic_derivatives_match_centered_value_differences": True,
            "complete_7x7_matrix_derivative_checked": True,
            "theorem_aligned_scalar_derivatives_checked": True,
            "derivative_continuation_checked_only_at_zero_weight_seams_14_15": True
        },
        "nonclaims": fixture["nonclaims"],
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
