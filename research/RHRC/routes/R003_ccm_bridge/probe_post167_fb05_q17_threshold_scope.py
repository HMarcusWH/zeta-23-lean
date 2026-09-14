#!/usr/bin/env python3
"""Floating two-sided log(q) microscope and next-cell scout for FB-05.

Discovery only.  The script follows the physical canonical matrix across the
Q=q-1 to Q=q cutoff transition and separately checks that the isolated entering
prime-power atom approaches the exact boundary-flat moment-jet prediction.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

from canonical_source_numeric import fixed_cell_bounds
from post167_fb05_threshold_jet import (
    aperture_from_source_coordinate,
    predicted_canonical_leading_matrix_float,
    restricted_canonical_entering_atom_float,
    successor_barrier_at_L_float,
    von_mangoldt_weight_float,
)


def _compact(rec: dict) -> dict:
    return {
        "L": rec["L"],
        "min_eigenvalue": rec["min_eigenvalue"],
        "normalized_min_eigenvalue": rec["normalized_min_eigenvalue"],
        "raw_leading_principal_determinants": rec["raw_leading_principal_determinants"],
        "final_sylvester_pivot": rec["final_sylvester_pivot"],
        "normalized_determinant": rec["normalized_determinant"],
    }


def _frobenius_relative(A: np.ndarray, B: np.ndarray) -> float:
    den = max(float(np.linalg.norm(B, ord="fro")), 1e-300)
    return float(np.linalg.norm(A - B, ord="fro")) / den


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=17)
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--parity", choices=["even", "odd"], default="odd")
    ap.add_argument("--grid", type=int, default=65)
    ap.add_argument("--local-seeds", type=int, default=6)
    ap.add_argument("--exponents", default="6,8,10,12,16,20,24,28,32")
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST167_FB05_Q17_THRESHOLD_DISCOVERY.json"))
    args = ap.parse_args()
    if args.q < 2 or args.grid < 9:
        raise ValueError("require q>=2 and grid>=9")
    exponents = sorted({int(x) for x in args.exponents.split(",") if x.strip()})
    if not exponents or min(exponents) < 2:
        raise ValueError("need source-offset exponents >=2")

    K = args.n + 1
    threshold = math.log(float(args.q))
    weight = von_mangoldt_weight_float(args.q)

    microscope = []
    for sign in (-1, 1):
        side = "left" if sign < 0 else "right"
        physical_Q = args.q - 1 if sign < 0 else args.q
        for k in exponents:
            omega = sign * (2.0 ** (-k))
            L = aperture_from_source_coordinate(args.q, omega)
            rec = successor_barrier_at_L_float(L, args.n, args.parity)
            microscope.append(
                {
                    "side": side,
                    "physical_Q": physical_Q,
                    "exponent": k,
                    "omega": omega,
                    **_compact(rec),
                }
            )

    # Isolated entering-atom asymptotics in both parity carriers.  Divide by
    # the predicted first surviving power before comparing to the exact leading
    # rank-one moment coefficient.
    atom_asymptotics = []
    for parity, order in (("odd", 7), ("even", 9)):
        predicted = predicted_canonical_leading_matrix_float(args.q, K, parity)
        for k in exponents:
            omega = 2.0 ** (-k)
            restricted = restricted_canonical_entering_atom_float(args.q, K, parity, omega)
            scaled = restricted / (omega ** order)
            atom_asymptotics.append(
                {
                    "parity": parity,
                    "order": order,
                    "exponent": k,
                    "omega": omega,
                    "scaled_frobenius_norm": float(np.linalg.norm(scaled, ord="fro")),
                    "predicted_frobenius_norm": float(np.linalg.norm(predicted, ord="fro")),
                    "relative_error_to_predicted": _frobenius_relative(scaled, predicted),
                    "numerical_rank_scaled": int(np.linalg.matrix_rank(scaled, tol=max(np.linalg.norm(scaled, 2), 1.0) * 1e-10)),
                }
            )

    # Full physical Q=q cell scout.  Stay strictly inside the cell; the exact
    # threshold is handled independently by the Arb replay.
    lo, hi = fixed_cell_bounds(args.q)
    eps = 2.0 ** -30
    cache: dict[float, dict] = {}

    def evaluate_t(t: float) -> dict:
        t = min(1.0 - eps, max(eps, float(t)))
        key = round(t, 16)
        if key not in cache:
            L = lo + t * (hi - lo)
            rec = successor_barrier_at_L_float(L, args.n, args.parity)
            cache[key] = {"t": t, **rec}
        return cache[key]

    ts = np.linspace(eps, 1.0 - eps, args.grid)
    rows = [evaluate_t(float(t)) for t in ts]
    rows_by_eig = sorted(rows, key=lambda r: float(r["normalized_min_eigenvalue"]))
    rows_by_pivot = sorted(
        [r for r in rows if r["final_sylvester_pivot"] is not None],
        key=lambda r: float(r["final_sylvester_pivot"]),
    )
    dt = 1.0 / (args.grid - 1)
    local_minima = []
    for seed in rows_by_eig[: args.local_seeds]:
        center = float(seed["t"])
        a = max(eps, center - 2.0 * dt)
        b = min(1.0 - eps, center + 2.0 * dt)
        if not a < b:
            continue
        eig_opt = minimize_scalar(
            lambda t: float(evaluate_t(t)["normalized_min_eigenvalue"]),
            bounds=(a, b), method="bounded", options={"xatol": 1e-14},
        )
        pivot_opt = minimize_scalar(
            lambda t: float(evaluate_t(t)["final_sylvester_pivot"])
            if evaluate_t(t)["final_sylvester_pivot"] is not None else math.inf,
            bounds=(a, b), method="bounded", options={"xatol": 1e-14},
        )
        local_minima.append(
            {
                "seed_t": center,
                "eigenvalue": {"success": bool(eig_opt.success), "t": float(eig_opt.x), "record": _compact(evaluate_t(float(eig_opt.x)))},
                "pivot": {"success": bool(pivot_opt.success), "t": float(pivot_opt.x), "record": _compact(evaluate_t(float(pivot_opt.x)))},
            }
        )

    all_rows = list(cache.values())
    negative = [r for r in all_rows if float(r["min_eigenvalue"]) < 0.0]
    best_eig = min(all_rows, key=lambda r: float(r["normalized_min_eigenvalue"]))
    best_pivot = min(
        [r for r in all_rows if r["final_sylvester_pivot"] is not None],
        key=lambda r: float(r["final_sylvester_pivot"]),
    )

    if negative:
        crossing = "CROSSES_NEGATIVE"
    else:
        right_reliable = {r["exponent"]: r for r in microscope if r["side"] == "right" and r["exponent"] <= 20}
        near = right_reliable.get(20)
        farther = right_reliable.get(16)
        if near and farther:
            delta = float(farther["min_eigenvalue"]) - float(near["min_eigenvalue"])
            scale = max(abs(float(near["min_eigenvalue"])), abs(float(farther["min_eigenvalue"])), 1e-30)
            if delta > 1e-7 * scale:
                crossing = "THRESHOLD_TURNS_UP"
            elif delta < -1e-7 * scale:
                crossing = "CONTINUES_DOWN_BUT_POSITIVE"
            else:
                crossing = "NO_CLEAR_TREND"
        else:
            crossing = "NO_CLEAR_TREND"

    payload = {
        "schema_version": "POST167_FB05_Q17_THRESHOLD_DISCOVERY_v1",
        "status": "PASS",
        "phase": "FLOATING_THRESHOLD_FALSIFICATION",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "target": {"q": args.q, "threshold_L": threshold, "N": args.n, "Kstar": K, "parity": args.parity},
        "von_mangoldt_weight": weight,
        "microscope": microscope,
        "isolated_atom_asymptotics": atom_asymptotics,
        "q17_cell": {
            "grid_points": args.grid,
            "unique_evaluations": len(cache),
            "negative_record_count": len(negative),
            "best_normalized_min_eigenvalue": {"t": best_eig["t"], **_compact(best_eig)},
            "best_final_sylvester_pivot": {"t": best_pivot["t"], **_compact(best_pivot)},
            "local_minima": local_minima,
        },
        "crossing_classification": crossing,
        "nonclaims": [
            "Floating threshold behavior is not a sign theorem.",
            "No sampled negative point does not imply Q17-cell positivity.",
            "The isolated-atom jet does not determine the full canonical derivative by itself.",
            "Any negative candidate requires independent Arb replay.",
            "RH remains OPEN.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "target": payload["target"],
        "crossing_classification": crossing,
        "q17_negative_record_count": len(negative),
        "best_normalized_min_eigenvalue": payload["q17_cell"]["best_normalized_min_eigenvalue"],
        "best_final_sylvester_pivot": payload["q17_cell"]["best_final_sylvester_pivot"],
        "atom_asymptotics_tail": atom_asymptotics[-4:],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
