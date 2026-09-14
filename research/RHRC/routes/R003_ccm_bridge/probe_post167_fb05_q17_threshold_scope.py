#!/usr/bin/env python3
"""Floating two-sided log(q) microscope and next-cell scout for FB-05.

Discovery only.  The physical canonical matrix is scouted in ordinary floating
arithmetic, while the isolated entering-atom asymptotics use high-precision
mpmath so division by omega^7 / omega^9 is not destroyed by cancellation.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import minimize_scalar

from canonical_source_numeric import fixed_cell_bounds
from post150_selected_residual import exact_parity_basis
from post167_fb05_threshold_jet import (
    aperture_from_source_coordinate,
    centered_moment_row,
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


def _mp_von_mangoldt_weight(q: int) -> mp.mpf:
    fac = sp.factorint(int(q))
    if len(fac) != 1:
        return mp.mpf("0")
    p = next(iter(fac))
    return mp.log(p) / mp.sqrt(q)


def _source_entry_mp(omega: mp.mpf, n: int, m: int) -> mp.mpf:
    if n == m:
        return 2 * omega * mp.cos(2 * mp.pi * n * omega)
    return (
        mp.sin(2 * mp.pi * n * omega) - mp.sin(2 * mp.pi * m * omega)
    ) / (mp.pi * (n - m))


def _restricted_entering_atom_mp(q: int, K: int, parity: str, omega: mp.mpf) -> mp.matrix:
    B = exact_parity_basis(K, parity)
    idx = list(range(-K, K + 1))
    weight = _mp_von_mangoldt_weight(q)
    out = mp.matrix(B.cols, B.cols)
    for a in range(B.cols):
        for b in range(B.cols):
            total = mp.mpf("0")
            for r, n in enumerate(idx):
                br = mp.mpf(int(B[r, a]))
                if not br:
                    continue
                for c, m in enumerate(idx):
                    bc = mp.mpf(int(B[c, b]))
                    if not bc:
                        continue
                    total += br * (-weight * _source_entry_mp(omega, n, m)) * bc
            out[a, b] = total
    return out


def _predicted_leading_mp(q: int, K: int, parity: str) -> tuple[int, mp.matrix]:
    B = exact_parity_basis(K, parity)
    weight = _mp_von_mangoldt_weight(q)
    if parity == "odd":
        order = 7
        row = centered_moment_row(K, B, 3)
        scalar = weight * 2 * (2 * mp.pi) ** 6 / math.factorial(7)
    elif parity == "even":
        order = 9
        row = centered_moment_row(K, B, 4)
        scalar = -weight * 2 * (2 * mp.pi) ** 8 / math.factorial(9)
    else:
        raise ValueError("parity must be even or odd")
    out = mp.matrix(B.cols, B.cols)
    for a in range(B.cols):
        for b in range(B.cols):
            out[a, b] = scalar * mp.mpf(int(row[0, a])) * mp.mpf(int(row[0, b]))
    return order, out


def _mp_frobenius(A: mp.matrix) -> mp.mpf:
    return mp.sqrt(mp.fsum(A[r, c] ** 2 for r in range(A.rows) for c in range(A.cols)))


def _atom_asymptotic_record(q: int, K: int, parity: str, exponent: int) -> dict:
    order, predicted = _predicted_leading_mp(q, K, parity)
    omega = mp.mpf(1) / (mp.mpf(2) ** exponent)
    restricted = _restricted_entering_atom_mp(q, K, parity, omega)
    scaled = restricted / (omega ** order)
    diff = scaled - predicted
    pred_norm = _mp_frobenius(predicted)
    scaled_norm = _mp_frobenius(scaled)
    rel = _mp_frobenius(diff) / pred_norm if pred_norm else mp.mpf("0")
    return {
        "parity": parity,
        "order": order,
        "exponent": exponent,
        "omega": mp.nstr(omega, 30),
        "scaled_frobenius_norm": mp.nstr(scaled_norm, 40),
        "predicted_frobenius_norm": mp.nstr(pred_norm, 40),
        "relative_error_to_predicted": mp.nstr(rel, 40),
        "arithmetic": "mpmath_160_dps",
    }


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

    # High-precision isolated entering-atom asymptotics.  This is separate from
    # the production scout so the tiny omega^9 even signal is not divided out of
    # double-precision cancellation noise.
    mp.mp.dps = 160
    atom_asymptotics = []
    for parity in ("odd", "even"):
        for k in exponents:
            atom_asymptotics.append(_atom_asymptotic_record(args.q, K, parity, k))

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
        "schema_version": "POST167_FB05_Q17_THRESHOLD_DISCOVERY_v2",
        "status": "PASS",
        "phase": "FLOATING_THRESHOLD_FALSIFICATION_WITH_HIGH_PRECISION_ATOM_JET",
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
            "High-precision isolated-atom asymptotics are not a proof of the full canonical derivative.",
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
