#!/usr/bin/env python3
"""Floating full-cell scout for the post-#166 FB-05 determinant barrier.

This deliberately attacks the Q=16, N=3, odd near-critical successor by
searching the entire fixed cutoff cell in the normalized cell coordinate t.
Floating optimization is discovery only; any sign claim must be replayed with
Arb by certify_post166_fb05_cell_barrier_scope.py.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

from post166_fb05_cell_interval import successor_barrier_float


def _finite_value(rec: dict, key: str, fallback: float = math.inf) -> float:
    value = rec.get(key)
    return float(value) if value is not None and math.isfinite(float(value)) else fallback


def _compact(rec: dict) -> dict:
    return {
        "t": rec["t"],
        "L": rec["L"],
        "min_eigenvalue": rec["min_eigenvalue"],
        "normalized_min_eigenvalue": rec["normalized_min_eigenvalue"],
        "condition_ratio": rec["condition_ratio"],
        "orthonormal_normalized_determinant": rec["orthonormal_normalized_determinant"],
        "raw_leading_principal_determinants": rec["raw_leading_principal_determinants"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=16)
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--parity", choices=["even", "odd"], default="odd")
    ap.add_argument("--grid", type=int, default=257)
    ap.add_argument("--top", type=int, default=12)
    ap.add_argument("--local-seeds", type=int, default=8)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST166_FB05_CELL_BARRIER_DISCOVERY.json"),
    )
    args = ap.parse_args()
    if args.grid < 9:
        raise ValueError("grid must be at least 9")

    cache: dict[float, dict] = {}

    def evaluate(t: float) -> dict:
        t = min(1.0, max(0.0, float(t)))
        key = round(t, 16)
        if key not in cache:
            cache[key] = successor_barrier_float(args.q, args.n, args.parity, t)
        return cache[key]

    ts = np.linspace(0.0, 1.0, args.grid)
    rows = [evaluate(float(t)) for t in ts]
    rows_by_margin = sorted(
        rows,
        key=lambda r: abs(_finite_value(r, "normalized_min_eigenvalue")),
    )

    sign_changes = []
    for left, right in zip(rows[:-1], rows[1:]):
        a = _finite_value(left, "min_eigenvalue")
        b = _finite_value(right, "min_eigenvalue")
        if math.isfinite(a) and math.isfinite(b) and (a == 0.0 or b == 0.0 or a * b < 0.0):
            sign_changes.append({"left": _compact(left), "right": _compact(right)})

    local_minima = []
    dt = 1.0 / (args.grid - 1)
    for seed in rows_by_margin[: args.local_seeds]:
        center = float(seed["t"])
        lo = max(0.0, center - 2.0 * dt)
        hi = min(1.0, center + 2.0 * dt)
        if not lo < hi:
            continue

        def eig_objective(t: float) -> float:
            return _finite_value(evaluate(t), "normalized_min_eigenvalue")

        def det_objective(t: float) -> float:
            return _finite_value(evaluate(t), "orthonormal_normalized_determinant")

        eig_opt = minimize_scalar(eig_objective, bounds=(lo, hi), method="bounded", options={"xatol": 1e-14})
        det_opt = minimize_scalar(det_objective, bounds=(lo, hi), method="bounded", options={"xatol": 1e-14})
        local_minima.append(
            {
                "seed_t": center,
                "bounds": [lo, hi],
                "eigenvalue_optimizer": {
                    "success": bool(eig_opt.success),
                    "t": float(eig_opt.x),
                    "record": _compact(evaluate(float(eig_opt.x))),
                },
                "determinant_optimizer": {
                    "success": bool(det_opt.success),
                    "t": float(det_opt.x),
                    "record": _compact(evaluate(float(det_opt.x))),
                },
            }
        )

    all_records = list(cache.values())
    best_eig = min(all_records, key=lambda r: _finite_value(r, "normalized_min_eigenvalue"))
    best_det = min(all_records, key=lambda r: _finite_value(r, "orthonormal_normalized_determinant"))
    negative_records = [r for r in all_records if _finite_value(r, "min_eigenvalue") < 0.0]

    payload = {
        "schema_version": "POST166_FB05_CELL_BARRIER_DISCOVERY_v1",
        "status": "PASS",
        "phase": "FLOATING_FULL_CELL_FALSIFICATION",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "target": {"Q": args.q, "N": args.n, "Kstar": args.n + 1, "parity": args.parity},
        "search": {
            "grid_points": args.grid,
            "unique_evaluations": len(cache),
            "local_seed_count": args.local_seeds,
        },
        "best_normalized_min_eigenvalue": _compact(best_eig),
        "best_normalized_determinant": _compact(best_det),
        "sampled_sign_changes": sign_changes,
        "negative_record_count": len(negative_records),
        "top_closest_to_zero": [_compact(r) for r in rows_by_margin[: args.top]],
        "local_minima": local_minima,
        "nonclaims": [
            "Floating minimization is not a global minimum certificate.",
            "No sampled sign change does not imply whole-cell positivity.",
            "A negative floating candidate must be replayed with Arb before promotion.",
            "No finite numerical result is Lean theorem authority.",
            "RH remains OPEN.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": "PASS",
                "target": payload["target"],
                "unique_evaluations": len(cache),
                "negative_record_count": len(negative_records),
                "sampled_sign_change_count": len(sign_changes),
                "best_normalized_min_eigenvalue": payload["best_normalized_min_eigenvalue"],
                "best_normalized_determinant": payload["best_normalized_determinant"],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
