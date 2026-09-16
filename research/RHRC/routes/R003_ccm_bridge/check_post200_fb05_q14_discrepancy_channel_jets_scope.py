#!/usr/bin/env python3
"""Independent implementation checks for post-#200 paired discrepancy jets."""
from __future__ import annotations

import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR
from post200_fb05_q14_discrepancy_channel_jets import (
    PAIRED_CHANNELS,
    paired_discrepancy_channel_jets,
    paired_reconstruction_ok,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post200_fb05_q14_discrepancy_mechanism_v1.json"
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
        analytic = paired_discrepancy_channel_jets(L, TARGET_KSTAR, Q)
        if not paired_reconstruction_ok(analytic):
            raise AssertionError(f"paired D+A reconstruction failed at {label}")

        checks = {}
        for channel in PAIRED_CHANNELS:
            ladder = []
            for hb in h_bits:
                h = arb(1) / (1 << hb)
                plus = paired_discrepancy_channel_jets(L + h, TARGET_KSTAR, Q)
                minus = paired_discrepancy_channel_jets(L - h, TARGET_KSTAR, Q)
                fd1 = (
                    plus["channels"][channel]["matrix_prime"]
                    - minus["channels"][channel]["matrix_prime"]
                ) * (arb(1) / (2 * h))
                exact = analytic["channels"][channel]["matrix_second"]
                ladder.append({
                    "h_bit": hb,
                    "from_first_ok": _matrix_agreement(exact, fd1, atol, rtol),
                })

            h = arb(1) / (1 << h_bits[-1])
            plus = paired_discrepancy_channel_jets(L + h, TARGET_KSTAR, Q)
            minus = paired_discrepancy_channel_jets(L - h, TARGET_KSTAR, Q)
            fd2 = (
                plus["channels"][channel]["matrix"]
                - analytic["channels"][channel]["matrix"] * 2
                + minus["channels"][channel]["matrix"]
            ) * (arb(1) / (h * h))
            value_ok = _matrix_agreement(
                analytic["channels"][channel]["matrix_second"], fd2, atol, rtol
            )
            if not ladder[-1]["from_first_ok"] or not value_ok:
                raise AssertionError(f"paired second derivative mismatch: {label} {channel}")
            checks[channel] = {
                "first_derivative_difference_ladder": ladder,
                "value_second_difference_final_ok": value_ok,
            }

        rows.append({
            "label": label,
            "Q": Q,
            "L": ball_record(L),
            "paired_reconstruction": analytic["paired_reconstruction"],
            "paired_channel_second_derivative_checks": checks,
        })

    print(json.dumps({
        "schema_version": "POST200_FB05_Q14_DISCREPANCY_CHANNEL_JET_CHECK_v1",
        "status": "PASS",
        "paired_channels": list(PAIRED_CHANNELS),
        "points": rows,
        "checks": {
            "pairing_occurs_at_matrix_jet_level": True,
            "paired_M_Mprime_Msecond_reconstruction_required": True,
            "paired_second_matches_first_derivative_differences": True,
            "paired_second_matches_value_second_differences": True
        },
        "theorem_promotion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
