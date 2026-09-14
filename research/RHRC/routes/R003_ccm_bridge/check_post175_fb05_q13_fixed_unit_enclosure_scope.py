#!/usr/bin/env python3
"""Deterministic acceptance checks for the post-#175 fixed-unit q13 benchmark."""
from __future__ import annotations

import json
from pathlib import Path

from flint import arb

from canonical_source_arb import alpha_L, beta_L, set_precision, source_eq44_gamma_L
from post166_fb05_cell_interval import cell_coordinate_L_arb, fixed_q_canonical_source_matrix_arb
from post173_fb05_q13_scalar_barrier import scalar_record_arb_at_L, seam_overlap_record, zero_weight_inertness_record
from post175_fb05_q13_fixed_unit_enclosure import (
    fixed_unit_alpha_L,
    fixed_unit_beta_L,
    fixed_unit_fixed_q_canonical_source_matrix_arb,
    fixed_unit_scalar_record_arb_at_L,
    fixed_unit_seam_overlap_record,
    fixed_unit_source_eq44_gamma_L,
    matrix_overlap,
    overlap,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post175_fb05_q13_fixed_unit_enclosure_v1.json"


def _quantized_t(value: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(value) * den))
    num = max(1, min(den - 1, num))
    return num, den


def _point_agreement(point: dict, fixture: dict) -> dict:
    bits = int(fixture["point_quantization_bits"])
    num, den = _quantized_t(float(point["t"]), bits)
    t = arb(num) / den
    Q = int(point["Q"])
    L = cell_coordinate_L_arb(Q, t)
    n_min = int(fixture["primitive_n_min"])
    n_max = int(fixture["primitive_n_max"])

    primitive_rows = []
    for n in range(n_min, n_max + 1):
        old_a, new_a = alpha_L(n, L), fixed_unit_alpha_L(n, L)
        old_b, new_b = beta_L(n, L), fixed_unit_beta_L(n, L)
        old_g, new_g = source_eq44_gamma_L(n, L), fixed_unit_source_eq44_gamma_L(n, L)
        row = {
            "n": n,
            "alpha_overlap": overlap(old_a, new_a),
            "beta_overlap": overlap(old_b, new_b),
            "gamma_overlap": overlap(old_g, new_g),
        }
        if not all(row[k] for k in ("alpha_overlap", "beta_overlap", "gamma_overlap")):
            raise AssertionError(f"fixed-unit primitive mismatch at {point['label']} n={n}: {row}")
        primitive_rows.append(row)

    old_M = fixed_q_canonical_source_matrix_arb(L, 3, Q)
    new_M = fixed_unit_fixed_q_canonical_source_matrix_arb(L, 3, Q)
    if not matrix_overlap(old_M, new_M):
        raise AssertionError(f"fixed-unit 7x7 matrix mismatch at {point['label']}")

    old_s = scalar_record_arb_at_L(Q, L)
    new_s = fixed_unit_scalar_record_arb_at_L(Q, L)
    scalar_fields = {
        "even_a": overlap(old_s["even"]["a"], new_s["even"]["a"]),
        "even_b": overlap(old_s["even"]["b"], new_s["even"]["b"]),
        "even_d": overlap(old_s["even"]["d"], new_s["even"]["d"]),
        "even_delta2": overlap(old_s["even"]["delta2"], new_s["even"]["delta2"]),
        "odd_N2_predecessor": overlap(old_s["odd_N2_predecessor"], new_s["odd_N2_predecessor"]),
    }
    if not all(scalar_fields.values()):
        raise AssertionError(f"fixed-unit scalar mismatch at {point['label']}: {scalar_fields}")

    return {
        "label": point["label"],
        "Q": Q,
        "t_num": num,
        "t_den": den,
        "primitive_rows": primitive_rows,
        "matrix_7x7_all_entries_overlap": True,
        "scalar_overlaps": scalar_fields,
    }


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    set_precision(int(fixture["arb_precision_bits"]))

    if fixture["selected_target"] != {
        "q_start": 13,
        "q_end": 16,
        "predecessor_N": 2,
        "successor_K": 3,
        "selected_parity": "even",
    }:
        raise AssertionError("q13 target fixture regression")

    inert = zero_weight_inertness_record()
    if not inert["von_mangoldt_14_zero"] or not inert["von_mangoldt_15_zero"]:
        raise AssertionError("Q14/Q15 zero-von-Mangoldt inertness regression")

    agreements = [_point_agreement(p, fixture) for p in fixture["agreement_points"]]

    old_seams = [seam_overlap_record(k) for k in (13, 14, 15, 16)]
    new_seams = [fixed_unit_seam_overlap_record(k) for k in (13, 14, 15, 16)]
    if not all(r["all_overlap"] for r in old_seams):
        raise AssertionError("baseline seam regression")
    if not all(r["all_overlap"] for r in new_seams):
        raise AssertionError("fixed-unit seam regression")

    payload = {
        "schema_version": "POST175_FB05_Q13_FIXED_UNIT_ENCLOSURE_CHECK_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_IMPLEMENTATION_AGREEMENT_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "agreement_points": agreements,
        "zero_weight_inertness": inert,
        "baseline_seams": old_seams,
        "fixed_unit_seams": new_seams,
        "checks": {
            "fixed_unit_primitives_overlap_direct_production_at_frozen_points": True,
            "full_7x7_canonical_matrices_overlap_at_frozen_points": True,
            "theorem_aligned_even_and_odd_scalar_observables_overlap": True,
            "Q14_Q15_von_mangoldt_weights_zero": True,
            "baseline_and_fixed_unit_threshold_continuations_overlap": True,
        },
        "nonclaims": fixture["nonclaims"],
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
