#!/usr/bin/env python3
"""Independent implementation checks for post-#198 four-way channel M''."""
from __future__ import annotations

import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR
from post187_fb05_q14_mixed_drift_selector import c_correction_prime
from post198_fb05_q14_four_way_channel_second_derivative import (
    CHANNEL_NAMES,
    c_correction_second_derivative,
    direct_baseline_value_channel_overlaps,
    fixed_unit_four_way_channel_jets,
    four_way_second_derivative_seam_overlap_record,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post198_fb05_q14_parity_source_mechanism_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def _agreement(exact: arb, numeric: arb, atol: float, rtol: float) -> bool:
    err = abs(exact - numeric)
    tol = arb(str(atol)) + arb(str(rtol)) * (arb(1) + abs(exact))
    return bool(err < tol)


def _matrix_agreement(exact, numeric, atol: float, rtol: float) -> bool:
    if exact.nrows() != numeric.nrows() or exact.ncols() != numeric.ncols():
        return False
    return all(
        _agreement(exact[r, c], numeric[r, c], atol, rtol)
        for r in range(exact.nrows())
        for c in range(exact.ncols())
    )


def _quantized_t(value: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(value) * den))
    return max(1, min(den - 1, num)), den


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))
    set_precision(int(fixture["implementation_check_precision_bits"]))
    points = {row["label"]: row for row in source["derivative_check_points"]}
    h_bits = [int(x) for x in fixture["second_derivative_h_bits"]]
    atol = float(fixture["second_derivative_absolute_tolerance"])
    rtol = float(fixture["second_derivative_relative_tolerance"])
    point_bits = int(source["point_quantization_bits"])
    rows = []

    for label in fixture["second_derivative_check_labels"]:
        point = points[label]
        num, den = _quantized_t(float(point["t"]), point_bits)
        Q = int(point["Q"])
        L = cell_coordinate_L_arb(Q, arb(num) / den)
        analytic = fixed_unit_four_way_channel_jets(L, TARGET_KSTAR, Q)
        if not all(analytic["reconstruction"].values()):
            raise AssertionError(f"four-way reconstruction failed at {label}")
        baseline = direct_baseline_value_channel_overlaps(L, TARGET_KSTAR, Q)
        if not all(baseline.values()):
            raise AssertionError(f"fixed-unit/direct value-channel baseline mismatch at {label}")

        channel_checks = {}
        for channel in CHANNEL_NAMES:
            ladder = []
            for hb in h_bits:
                h = arb(1) / (1 << hb)
                plus = fixed_unit_four_way_channel_jets(L + h, TARGET_KSTAR, Q)
                minus = fixed_unit_four_way_channel_jets(L - h, TARGET_KSTAR, Q)
                fd1 = (plus["channels"][channel]["matrix_prime"] - minus["channels"][channel]["matrix_prime"]) * (arb(1) / (2 * h))
                exact = analytic["channels"][channel]["matrix_second"]
                ladder.append({"h_bit": hb, "from_first_ok": _matrix_agreement(exact, fd1, atol, rtol)})
            h = arb(1) / (1 << h_bits[-1])
            plus = fixed_unit_four_way_channel_jets(L + h, TARGET_KSTAR, Q)
            minus = fixed_unit_four_way_channel_jets(L - h, TARGET_KSTAR, Q)
            center = analytic
            fd2 = (
                plus["channels"][channel]["matrix"]
                - center["channels"][channel]["matrix"] * 2
                + minus["channels"][channel]["matrix"]
            ) * (arb(1) / (h * h))
            value_ok = _matrix_agreement(exact, fd2, atol, rtol)
            if not ladder[-1]["from_first_ok"] or not value_ok:
                raise AssertionError(f"four-way second derivative mismatch: {label} {channel}")
            channel_checks[channel] = {
                "first_derivative_difference_ladder": ladder,
                "value_second_difference_final_ok": value_ok,
            }

        scalar_ladder = []
        exact_scalar = c_correction_second_derivative(L)
        for hb in h_bits:
            h = arb(1) / (1 << hb)
            numeric = (c_correction_prime(L + h) - c_correction_prime(L - h)) / (2 * h)
            scalar_ladder.append({"h_bit": hb, "ok": _agreement(exact_scalar, numeric, atol, rtol)})
        if not scalar_ladder[-1]["ok"]:
            raise AssertionError(f"cCorrection'' mismatch at {label}")

        rows.append({
            "label": label,
            "Q": Q,
            "L": ball_record(L),
            "direct_value_channel_overlaps": baseline,
            "channel_second_derivative_checks": channel_checks,
            "c_correction_second_derivative_ladder": scalar_ladder,
        })

    seams = [four_way_second_derivative_seam_overlap_record(k, TARGET_KSTAR) for k in (14, 15)]
    if not all(row["all_overlap"] for row in seams):
        raise AssertionError("four-way second-derivative seam regression")

    print(json.dumps({
        "schema_version": "POST198_FB05_Q14_FOUR_WAY_SECOND_DERIVATIVE_CHECK_v1",
        "status": "PASS",
        "points": rows,
        "zero_weight_seams": seams,
        "checks": {
            "four_way_value_matches_direct_baseline": True,
            "four_way_second_matches_first_derivative_differences": True,
            "four_way_second_matches_value_second_differences": True,
            "scalar_shift_second_independently_checked": True,
            "total_M_Mprime_Msecond_reconstruction_required": True,
        },
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
