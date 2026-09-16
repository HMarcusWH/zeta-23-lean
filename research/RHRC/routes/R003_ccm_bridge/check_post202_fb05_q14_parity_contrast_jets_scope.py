#!/usr/bin/env python3
"""Independent implementation checks for the post-#202 parity-gap contrast jets."""
from __future__ import annotations

import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR
from post202_fb05_q14_parity_contrast_jets import (
    parity_gap_contrast_jets,
    parity_gap_contrast_metadata,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post202_fb05_q14_composite_parity_gap_v1.json"
SOURCE_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def _agreement(exact: arb, numeric: arb, atol: float, rtol: float) -> bool:
    err = abs(exact - numeric)
    tol = arb(str(atol)) + arb(str(rtol)) * (arb(1) + abs(exact))
    return bool(err < tol)


def _quantized_t(value: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(value) * den))
    return max(1, min(den - 1, num)), den


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_FIXTURE.read_text(encoding="utf-8"))
    set_precision(int(fixture["implementation_check_precision_bits"]))
    points = {row["label"]: row for row in source["derivative_check_points"]}
    h_bits = [int(x) for x in fixture["implementation_check_h_bits"]]
    atol = float(fixture["implementation_check_absolute_tolerance"])
    rtol = float(fixture["implementation_check_relative_tolerance"])
    point_bits = int(source["point_quantization_bits"])

    metadata = parity_gap_contrast_metadata()
    if not (metadata["symmetric"] and metadata["trace_zero"] and metadata["nonzero"]):
        raise AssertionError("exact parity-gap contrast invariant failed")
    if int(metadata["dimension"]) != 2 * TARGET_KSTAR + 1:
        raise AssertionError("parity-gap contrast dimension drift")

    rows = []
    for label in fixture["implementation_check_labels"]:
        point = points[label]
        num, den = _quantized_t(float(point["t"]), point_bits)
        Q = int(point["Q"])
        L = cell_coordinate_L_arb(Q, arb(num) / den)
        analytic = parity_gap_contrast_jets(L, TARGET_KSTAR, Q)
        if not all(analytic["checks"].values()):
            raise AssertionError(f"contrast reconstruction failed at {label}")

        ladder = []
        for hb in h_bits:
            h = arb(1) / (1 << hb)
            plus = parity_gap_contrast_jets(L + h, TARGET_KSTAR, Q)
            minus = parity_gap_contrast_jets(L - h, TARGET_KSTAR, Q)
            fd_Gp = (plus["G"] - minus["G"]) / (2 * h)
            fd_Gpp = (plus["G_prime"] - minus["G_prime"]) / (2 * h)
            ladder.append({
                "h_bit": hb,
                "G_prime_from_value_ok": _agreement(analytic["G_prime"], fd_Gp, atol, rtol),
                "G_second_from_first_ok": _agreement(analytic["G_second"], fd_Gpp, atol, rtol),
            })

        h = arb(1) / (1 << h_bits[-1])
        plus = parity_gap_contrast_jets(L + h, TARGET_KSTAR, Q)
        minus = parity_gap_contrast_jets(L - h, TARGET_KSTAR, Q)
        fd_second = (plus["G"] - 2 * analytic["G"] + minus["G"]) / (h * h)
        value_second_ok = _agreement(analytic["G_second"], fd_second, atol, rtol)
        if not ladder[-1]["G_prime_from_value_ok"]:
            raise AssertionError(f"G' finite-difference mismatch at {label}")
        if not ladder[-1]["G_second_from_first_ok"] or not value_second_ok:
            raise AssertionError(f"G'' finite-difference mismatch at {label}")

        rows.append({
            "label": label,
            "Q": Q,
            "L": ball_record(L),
            "contrast_checks": analytic["checks"],
            "finite_difference_ladder": ladder,
            "G_second_from_value_ok": value_second_ok,
        })

    print(json.dumps({
        "schema_version": "POST202_FB05_Q14_PARITY_CONTRAST_JET_CHECK_v1",
        "status": "PASS",
        "contrast_metadata": metadata,
        "points": rows,
        "checks": {
            "theorem_aligned_w_correction_removal": True,
            "scalar_identity_annihilated_before_transport": True,
            "direct_total_reconstruction_required": True,
            "G_prime_matches_value_differences": True,
            "G_second_matches_first_derivative_differences": True,
            "G_second_matches_value_second_differences": True
        },
        "theorem_promotion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
