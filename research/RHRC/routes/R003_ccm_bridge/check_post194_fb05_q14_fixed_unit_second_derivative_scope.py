#!/usr/bin/env python3
"""Independent implementation checks for the post-#194 canonical second derivative."""
from __future__ import annotations

import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post175_fb05_q13_fixed_unit_enclosure import (
    fixed_unit_alpha_L,
    fixed_unit_beta_L,
    fixed_unit_fixed_q_canonical_source_matrix_arb,
    fixed_unit_source_eq44_gamma_L,
)
from post177_fb05_q13_fixed_unit_derivative import (
    fixed_unit_alpha_L_prime,
    fixed_unit_beta_L_prime,
    fixed_unit_derivative_scalar_record_arb_at_L,
    fixed_unit_source_eq44_gamma_L_prime,
)
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_alpha_L_second,
    fixed_unit_beta_L_second,
    fixed_unit_second_derivative_scalar_record_arb_at_L,
    fixed_unit_source_eq44_gamma_L_second,
    second_derivative_seam_overlap_record,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post194_fb05_q14_parity_trajectory_sharp_enclosure_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def _fd_first(func, L: arb, h: arb) -> arb:
    return (func(L + h) - func(L - h)) / (2 * h)


def _fd_second(func, L: arb, h: arb) -> arb:
    return (func(L + h) - 2 * func(L) + func(L - h)) / (h * h)


def _agreement_record(analytic: arb, numeric: arb, atol: float, rtol: float) -> dict:
    err = abs(analytic - numeric)
    tol = arb(str(atol)) + arb(str(rtol)) * (arb(1) + abs(analytic))
    return {
        "analytic": ball_record(analytic),
        "numeric": ball_record(numeric),
        "error": ball_record(err),
        "tolerance": ball_record(tol),
        "ok": bool(err < tol),
    }


def _assert_ok(rec: dict, context: str) -> None:
    if not rec["ok"]:
        raise AssertionError(f"second derivative implementation mismatch: {context}")


def _source_points(fixture: dict, source: dict) -> list[dict]:
    wanted = list(fixture["second_derivative_check_labels"])
    by_label = {row["label"]: row for row in source["derivative_check_points"]}
    if any(label not in by_label for label in wanted):
        raise AssertionError("second derivative check label missing from #177 fixture")
    return [by_label[label] for label in wanted]


def _quantized_t(value: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(value) * den))
    num = max(1, min(den - 1, num))
    return num, den


def _point_check(point: dict, fixture: dict, source: dict) -> dict:
    bits = int(source["point_quantization_bits"])
    num, den = _quantized_t(float(point["t"]), bits)
    Q = int(point["Q"])
    L = cell_coordinate_L_arb(Q, arb(num) / den)
    h_bits = [int(x) for x in fixture["second_derivative_h_bits"]]
    rtol = float(fixture["second_derivative_relative_tolerance"])
    atol = float(fixture["second_derivative_absolute_tolerance"])
    n_values = [int(x) for x in source["derivative_check_n_values"]]

    analytic = fixed_unit_second_derivative_scalar_record_arb_at_L(Q, L)
    primitive_rows = []
    primitive_funcs = {
        "alpha": (
            fixed_unit_alpha_L,
            fixed_unit_alpha_L_prime,
            fixed_unit_alpha_L_second,
        ),
        "beta": (
            fixed_unit_beta_L,
            fixed_unit_beta_L_prime,
            fixed_unit_beta_L_second,
        ),
        "gamma": (
            fixed_unit_source_eq44_gamma_L,
            fixed_unit_source_eq44_gamma_L_prime,
            fixed_unit_source_eq44_gamma_L_second,
        ),
    }

    for n in n_values:
        row = {"n": n}
        for name, (value_func, first_func, second_func) in primitive_funcs.items():
            exact_second = second_func(n, L)
            first_ladder = []
            for hb in h_bits:
                h = arb(1) / (1 << hb)
                fd = _fd_first(lambda x, f=first_func, nn=n: f(nn, x), L, h)
                rec = _agreement_record(exact_second, fd, atol, rtol)
                first_ladder.append({"h_bit": hb, **rec})
            _assert_ok(first_ladder[-1], f"{point['label']} {name} d(first)/dL")

            h = arb(1) / (1 << h_bits[-1])
            value_fd2 = _fd_second(lambda x, f=value_func, nn=n: f(nn, x), L, h)
            value_rec = _agreement_record(exact_second, value_fd2, atol, rtol)
            _assert_ok(value_rec, f"{point['label']} {name} second value difference")
            row[name] = {
                "first_derivative_difference_ladder": first_ladder,
                "value_second_difference_final": value_rec,
            }
        primitive_rows.append(row)

    h = arb(1) / (1 << h_bits[-1])
    plus = fixed_unit_derivative_scalar_record_arb_at_L(Q, L + h)
    minus = fixed_unit_derivative_scalar_record_arb_at_L(Q, L - h)
    matrix_first_checks = []
    for r in range(analytic["matrix_second"].nrows()):
        for c in range(r, analytic["matrix_second"].ncols()):
            fd = (plus["matrix_prime"][r, c] - minus["matrix_prime"][r, c]) / (2 * h)
            rec = _agreement_record(analytic["matrix_second"][r, c], fd, atol, rtol)
            _assert_ok(rec, f"{point['label']} M''[{r},{c}] from M'")
            matrix_first_checks.append({"r": r, "c": c, **rec})

    Mp = fixed_unit_fixed_q_canonical_source_matrix_arb(L + h, 3, Q)
    Mc = fixed_unit_fixed_q_canonical_source_matrix_arb(L, 3, Q)
    Mm = fixed_unit_fixed_q_canonical_source_matrix_arb(L - h, 3, Q)
    matrix_value_checks = []
    for r in range(analytic["matrix_second"].nrows()):
        for c in range(r, analytic["matrix_second"].ncols()):
            fd2 = (Mp[r, c] - 2 * Mc[r, c] + Mm[r, c]) / (h * h)
            rec = _agreement_record(analytic["matrix_second"][r, c], fd2, atol, rtol)
            _assert_ok(rec, f"{point['label']} M''[{r},{c}] from M")
            matrix_value_checks.append({"r": r, "c": c, **rec})

    scalar_pairs = {
        "even_a_second": (
            analytic["even"]["a_second"],
            (plus["even"]["a_prime"] - minus["even"]["a_prime"]) / (2 * h),
        ),
        "even_b_second": (
            analytic["even"]["b_second"],
            (plus["even"]["b_prime"] - minus["even"]["b_prime"]) / (2 * h),
        ),
        "even_d_second": (
            analytic["even"]["d_second"],
            (plus["even"]["d_prime"] - minus["even"]["d_prime"]) / (2 * h),
        ),
        "odd_N2_predecessor_second": (
            analytic["odd_N2_predecessor_second"],
            (
                plus["odd_N2_predecessor_prime"]
                - minus["odd_N2_predecessor_prime"]
            )
            / (2 * h),
        ),
    }
    scalar_checks = {}
    for name, (exact_second, fd) in scalar_pairs.items():
        rec = _agreement_record(exact_second, fd, atol, rtol)
        _assert_ok(rec, f"{point['label']} {name}")
        scalar_checks[name] = rec

    return {
        "label": point["label"],
        "Q": Q,
        "t_num": num,
        "t_den": den,
        "L": ball_record(L),
        "primitive_second_derivative_checks": primitive_rows,
        "matrix_second_from_matrix_prime_checks": matrix_first_checks,
        "matrix_second_from_value_checks": matrix_value_checks,
        "scalar_second_derivative_checks": scalar_checks,
    }


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))

    if fixture["selected_target"] != source["selected_target"]:
        raise AssertionError("second derivative selected target drift")
    if fixture["required_ancestry_control"] != source["required_ancestry_control"]:
        raise AssertionError("second derivative ancestry control drift")

    set_precision(int(fixture["implementation_check_precision_bits"]))
    checks = [_point_check(p, fixture, source) for p in _source_points(fixture, source)]
    seams = [
        second_derivative_seam_overlap_record(int(k))
        for k in source["required_derivative_zero_weight_seams"]
    ]
    if not all(row["all_overlap"] for row in seams):
        raise AssertionError("second derivative zero-weight seam regression")

    print(
        json.dumps(
            {
                "schema_version": "POST194_FB05_Q14_SECOND_DERIVATIVE_CHECK_v1",
                "status": "PASS",
                "claim_cap": "FINITE_SECOND_DERIVATIVE_IMPLEMENTATION_CHECK_ONLY",
                "points": checks,
                "zero_weight_second_derivative_seams": seams,
                "checks": {
                    "analytic_second_matches_first_derivative_differences": True,
                    "analytic_second_matches_value_second_differences": True,
                    "complete_7x7_matrix_second_derivative_checked": True,
                    "same_state_scalar_second_derivatives_checked": True,
                    "second_derivative_continuation_checked_only_at_zero_weight_seams_14_15": True,
                },
                "theorem_promotion": False,
                "rh_claim": False,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
