#!/usr/bin/env python3
"""Rigorous old-vs-fixed-unit interval-width benchmark for post-#175 FB-05.

A green run means the comparison executed faithfully.  The fixed-unit method may
be ACCEPTED, MIXED, or REJECTED while CI remains green.  Only evaluator mismatch,
seam/normalization regression, malformed benchmark schedule, or execution failure
is a red condition.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb, arb_mat

from canonical_source_arb import (
    alpha_L,
    ball_record,
    beta_L,
    direct_arch_component,
    pole_component,
    prime_component,
    set_precision,
    source_eq44_gamma_L,
)
from post166_fb05_cell_interval import _arb_matrix_from_sympy, arb_unit_interval, cell_coordinate_L_arb
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import scalar_geometry
from post175_fb05_q13_fixed_unit_enclosure import (
    fixed_unit_alpha_L,
    fixed_unit_beta_L,
    fixed_unit_source_eq44_gamma_L,
    matrix_overlap,
    overlap,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post175_fb05_q13_fixed_unit_enclosure_v1.json"


def _quantized_center(t: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(t) * den))
    num = max(1, min(den - 1, num))
    return num, den


def _expected_box(label: str, Q: int, t: float, radius_bit: int, point_bits: int, primary: bool) -> dict:
    if radius_bit >= point_bits:
        raise ValueError("radius_bit must be smaller than point quantization bits")
    center_num, den = _quantized_center(t, point_bits)
    radius_num = 1 << (point_bits - radius_bit)
    lo = max(0, center_num - radius_num)
    hi = min(den, center_num + radius_num)
    if not 0 <= lo < hi <= den:
        raise AssertionError("invalid expected benchmark box")
    return {
        "label": label,
        "Q": int(Q),
        "primary": bool(primary),
        "radius_bit": int(radius_bit),
        "lo_num": int(lo),
        "hi_num": int(hi),
        "den": int(den),
        "center_num": int(center_num),
    }


def expected_benchmark_boxes(fixture: dict) -> list[dict]:
    """Reconstruct the frozen #176 schedule directly from the fixture."""
    bits = int(fixture["point_quantization_bits"])
    boxes: list[dict] = []
    for center in fixture["primary_Q14_centers"]:
        for radius_bit in fixture["primary_radius_bits"]:
            boxes.append(_expected_box(
                f"{center['label']}_r2^-{int(radius_bit)}",
                int(center["Q"]), float(center["t"]), int(radius_bit), bits, True,
            ))
    for control in fixture["control_boxes"]:
        boxes.append(_expected_box(
            control["label"], int(control["Q"]), float(control["t"]),
            int(control["radius_bit"]), bits, False,
        ))
    return boxes


def validate_benchmark_schedule(fixture: dict, benchmark: dict) -> None:
    """Fail closed if a supplied PASS benchmark is not the frozen fixture schedule."""
    if benchmark.get("schema_version") != "POST175_FB05_Q13_FIXED_UNIT_BENCHMARK_v1":
        raise AssertionError("benchmark schema regression")
    if benchmark.get("status") != "PASS":
        raise AssertionError("benchmark schedule did not pass")
    for key in ("theorem_authority_pr", "research_anchor_pr", "routing_sync_pr"):
        if benchmark.get(key) != fixture.get(key):
            raise AssertionError(f"benchmark authority mismatch: {key}")

    expected = expected_benchmark_boxes(fixture)
    actual = benchmark.get("boxes")
    if not isinstance(actual, list):
        raise AssertionError("benchmark boxes missing")
    if len(actual) != len(expected):
        raise AssertionError("benchmark box count mismatch")

    expected_by_label = {b["label"]: b for b in expected}
    if len(expected_by_label) != len(expected):
        raise AssertionError("fixture produced duplicate expected labels")
    actual_labels = [b.get("label") for b in actual]
    if len(set(actual_labels)) != len(actual_labels):
        raise AssertionError("benchmark contains duplicate labels")
    if set(actual_labels) != set(expected_by_label):
        raise AssertionError("benchmark label set does not match frozen fixture")

    keys = ("label", "Q", "primary", "radius_bit", "lo_num", "hi_num", "den", "center_num")
    for box in actual:
        expected_box = expected_by_label[box["label"]]
        for key in keys:
            if box.get(key) != expected_box[key]:
                raise AssertionError(f"benchmark schedule mismatch for {box['label']} field {key}")

    primary_count = sum(1 for b in expected if b["primary"])
    control_count = len(expected) - primary_count
    if benchmark.get("primary_box_count") != primary_count:
        raise AssertionError("benchmark primary count mismatch")
    if benchmark.get("control_box_count") != control_count:
        raise AssertionError("benchmark control count mismatch")


def _width(x: arb) -> arb:
    return arb(x.upper()) - arb(x.lower())


def _width_comparison(old: arb, new: arb, factor: arb) -> dict:
    old_w = _width(old)
    new_w = _width(new)
    same_object_overlap = overlap(old, new)
    if not same_object_overlap:
        raise AssertionError("old/new interval enclosures are disjoint")
    strictly_narrower = bool(new_w < old_w)
    material = bool(factor * new_w <= old_w)
    if bool(new_w > 0):
        gain = old_w / new_w
        gain_record = ball_record(gain)
    else:
        gain_record = {"infinite_or_exact": True}
    return {
        "old": ball_record(old),
        "new": ball_record(new),
        "old_width": ball_record(old_w),
        "new_width": ball_record(new_w),
        "gain_old_over_new": gain_record,
        "overlap": same_object_overlap,
        "strictly_narrower": strictly_narrower,
        "material_gain": material,
    }


def _primitive_caches(L: arb, N: int, fixed_unit: bool) -> dict:
    idx = list(range(-N, N + 1))
    if fixed_unit:
        return {
            "alpha": {n: fixed_unit_alpha_L(n, L) for n in idx},
            "beta": {n: fixed_unit_beta_L(n, L) for n in idx},
            "gamma": {n: fixed_unit_source_eq44_gamma_L(n, L) for n in idx},
        }
    return {
        "alpha": {n: alpha_L(n, L) for n in idx},
        "beta": {n: beta_L(n, L) for n in idx},
        "gamma": {n: source_eq44_gamma_L(n, L) for n in idx},
    }


def _matrix_from_caches(L: arb, N: int, Q: int, caches: dict) -> arb_mat:
    idx = list(range(-N, N + 1))
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            value = (
                pole_component(n, m, L)
                - direct_arch_component(
                    n, m, L,
                    caches["alpha"], caches["beta"], caches["gamma"],
                )
                - prime_component(n, m, L, Q)
            )
            rows[r][c] = value
            rows[c][r] = value
    return arb_mat(rows)


def _restriction(M: arb_mat, parity: str) -> dict:
    geom = one_step_geometry(2, parity)
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * M * B
    norms = scalar_geometry(parity)
    a = H[0, 0]
    b = H[0, 1]
    d = H[1, 1]
    delta2 = a * d - b * b
    return {
        "H": H,
        "a": a,
        "b": b,
        "d": d,
        "delta2": delta2,
        "normalized_a": a / norms.W_norm_sq,
        "normalized_delta2": delta2 / (norms.W_norm_sq * norms.c_norm_sq),
    }


def _box_record(box: dict, fixture: dict) -> dict:
    Q = int(box["Q"])
    t = arb_unit_interval(int(box["lo_num"]), int(box["hi_num"]), int(box["den"]))
    L = cell_coordinate_L_arb(Q, t)
    factor = arb(str(fixture["material_width_gain_factor"]))

    old_cache = _primitive_caches(L, 3, False)
    new_cache = _primitive_caches(L, 3, True)

    primitives = []
    for n in range(-3, 4):
        primitives.append({
            "n": n,
            "alpha": _width_comparison(old_cache["alpha"][n], new_cache["alpha"][n], factor),
            "beta": _width_comparison(old_cache["beta"][n], new_cache["beta"][n], factor),
            "gamma": _width_comparison(old_cache["gamma"][n], new_cache["gamma"][n], factor),
        })

    old_M = _matrix_from_caches(L, 3, Q, old_cache)
    new_M = _matrix_from_caches(L, 3, Q, new_cache)
    if not matrix_overlap(old_M, new_M):
        raise AssertionError(f"matrix interval mismatch in {box['label']}")

    matrix_entries = []
    for r in range(old_M.nrows()):
        for c in range(r, old_M.ncols()):
            cmp = _width_comparison(old_M[r, c], new_M[r, c], factor)
            matrix_entries.append({"r": r, "c": c, **cmp})

    old_even = _restriction(old_M, "even")
    new_even = _restriction(new_M, "even")
    old_odd = _restriction(old_M, "odd")
    new_odd = _restriction(new_M, "odd")

    scalar_names = ("a", "b", "d", "delta2", "normalized_a", "normalized_delta2")
    even = {
        name: _width_comparison(old_even[name], new_even[name], factor)
        for name in scalar_names
    }
    odd_pred = _width_comparison(old_odd["a"], new_odd["a"], factor)

    if not all(overlap(old_even[name], new_even[name]) for name in scalar_names):
        raise AssertionError(f"even scalar interval mismatch in {box['label']}")
    if not overlap(old_odd["a"], new_odd["a"]):
        raise AssertionError(f"odd ancestry interval mismatch in {box['label']}")

    primitive_total = 3 * 7
    primitive_improved = sum(
        int(row[k]["strictly_narrower"])
        for row in primitives for k in ("alpha", "beta", "gamma")
    )
    matrix_improved = sum(int(row["strictly_narrower"]) for row in matrix_entries)

    return {
        "label": box["label"],
        "Q": Q,
        "primary": bool(box["primary"]),
        "radius_bit": int(box["radius_bit"]),
        "t_ball": ball_record(t),
        "L_ball": ball_record(L),
        "primitive_widths": primitives,
        "primitive_strict_improvement_count": primitive_improved,
        "primitive_comparison_count": primitive_total,
        "matrix_entry_widths": matrix_entries,
        "matrix_strict_improvement_count": matrix_improved,
        "matrix_comparison_count": len(matrix_entries),
        "even_scalar_widths": even,
        "odd_N2_predecessor_width": odd_pred,
        "primary_delta_strictly_narrower": even["delta2"]["strictly_narrower"],
        "primary_delta_material_gain": even["delta2"]["material_gain"],
    }


def _method_classification(records: list[dict]) -> str:
    primary = [r for r in records if r["primary"]]
    if not primary:
        raise AssertionError("no primary Q14 benchmark boxes")
    if all(r["primary_delta_material_gain"] for r in primary):
        return "FIXED_UNIT_METHOD_ACCEPTED"
    if any(r["primary_delta_strictly_narrower"] for r in primary):
        return "FIXED_UNIT_METHOD_MIXED"
    return "FIXED_UNIT_METHOD_REJECTED"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--benchmark", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST175_Q13_FIXED_UNIT_CERTIFICATE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    benchmark = json.loads(args.benchmark.read_text(encoding="utf-8"))
    set_precision(int(fixture["arb_precision_bits"]))

    validate_benchmark_schedule(fixture, benchmark)
    records = [_box_record(box, fixture) for box in benchmark["boxes"]]
    method = _method_classification(records)

    out = {
        "schema_version": "POST175_FB05_Q13_FIXED_UNIT_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_METHOD_COMPARISON_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": int(fixture["arb_precision_bits"]),
        "material_width_gain_factor": fixture["material_width_gain_factor"],
        "method_classification": method,
        "benchmark_schedule_bound_to_fixture": True,
        "boxes": records,
        "primary_summary": [
            {
                "label": r["label"],
                "radius_bit": r["radius_bit"],
                "delta_strictly_narrower": r["primary_delta_strictly_narrower"],
                "delta_material_gain": r["primary_delta_material_gain"],
            }
            for r in records if r["primary"]
        ],
        "nonclaims": fixture["nonclaims"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "method_classification": method,
        "benchmark_schedule_bound_to_fixture": True,
        "primary_summary": out["primary_summary"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
