#!/usr/bin/env python3
"""Post-#169 floating falsifier for Schur visibility and threshold/background competition.

Primary target: q=17, predecessor N=3, odd parity.  This script is discovery
only.  It uses the theorem-aligned [W|c] zero-shift Schur coordinate, filters
first-bad interpretations to H1 predecessor-positive states, and never treats
finite differences as derivative theorems.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

from canonical_source_numeric import canonical_source_matrix_L
from post167_fb05_threshold_jet import aperture_from_source_coordinate, von_mangoldt_weight_float
from post169_fb05_schur_visibility import (
    background_signed_channels_at_omega_float,
    directional_schur_derivative_float,
    full_background_at_omega_float,
    moment_vector_step,
    pivot_effect_record,
    restricted_step_matrix_float,
    schur_visibility_float,
    theorem_aligned_pivot_float,
    threshold_leading_scalar,
)


def next_von_mangoldt_threshold(q: int) -> int:
    k = q + 1
    while k < q + 10000:
        if von_mangoldt_weight_float(k) != 0.0:
            return k
        k += 1
    raise ArithmeticError("failed to find next von-Mangoldt threshold")


def _background_pivot(q: int, N: int, parity: str, omega: float) -> dict:
    state = full_background_at_omega_float(q, N, omega)
    rec = theorem_aligned_pivot_float(state["background"], N, parity)
    return {"omega": omega, "L": state["L"], **rec}


def _finite_difference_background(q: int, N: int, parity: str, exponent: int) -> dict:
    h = 2.0 ** (-int(exponent))
    minus = _background_pivot(q, N, parity, -h)
    plus = _background_pivot(q, N, parity, h)
    zero = _background_pivot(q, N, parity, 0.0)
    c2 = float(zero["geometry"].c2)
    beta_raw = (plus["raw_pivot"] - minus["raw_pivot"]) / (2.0 * h)
    beta_unit = beta_raw / c2

    channel_minus = background_signed_channels_at_omega_float(q, N, -h)
    channel_plus = background_signed_channels_at_omega_float(q, N, h)
    channel_contrib = {}
    total_direction = np.zeros_like(zero["H"])
    for name in ("pole", "arch_signed", "prime_signed", "scalar_shift"):
        Hm = restricted_step_matrix_float(channel_minus[name], zero["geometry"])
        Hp = restricted_step_matrix_float(channel_plus[name], zero["geometry"])
        D = (Hp - Hm) / (2.0 * h)
        total_direction += D
        channel_contrib[name] = directional_schur_derivative_float(zero["H"], D) / c2
    channel_sum = float(sum(channel_contrib.values()))
    directional_total = directional_schur_derivative_float(zero["H"], total_direction) / c2
    return {
        "exponent": exponent,
        "h": h,
        "H1_minus": minus["H1_predecessor_positive"],
        "H1_zero": zero["H1_predecessor_positive"],
        "H1_plus": plus["H1_predecessor_positive"],
        "beta_unit_central_difference": beta_unit,
        "channel_directional_contributions": channel_contrib,
        "channel_directional_sum": channel_sum,
        "directional_total": directional_total,
        "finite_difference_minus_directional_total": beta_unit - directional_total,
        "interpretation": "finite-difference evidence in source coordinate omega; not a derivative theorem",
    }


def _local_model(P0: float, beta: float, Kkick: float, order: int, omega_next: float) -> dict:
    out = {
        "P0": P0,
        "beta1": beta,
        "Kkick": Kkick,
        "order": order,
        "omega_next": omega_next,
        "omega_slope_catch": None,
        "omega_value_catch": None,
        "predicted_turning_point": None,
        "predicted_zero_before_next": None,
    }
    if beta < 0.0 and Kkick > 0.0:
        out["omega_slope_catch"] = (-beta / (order * Kkick)) ** (1.0 / (order - 1))
        out["omega_value_catch"] = (-beta / Kkick) ** (1.0 / (order - 1))
        out["predicted_turning_point"] = out["omega_slope_catch"]

        def f(w: float) -> float:
            return P0 + beta * w + Kkick * (w ** order)

        grid = np.linspace(0.0, omega_next, 257)
        vals = [f(float(w)) for w in grid]
        for a, b, fa, fb in zip(grid[:-1], grid[1:], vals[:-1], vals[1:]):
            if fa == 0.0:
                out["predicted_zero_before_next"] = float(a)
                break
            if fa * fb < 0.0:
                out["predicted_zero_before_next"] = float(brentq(f, float(a), float(b)))
                break
    return out


def _physical_scout(q: int, q_next: int, N: int, parity: str, grid: int) -> dict:
    lo = math.log(float(q))
    hi = math.log(float(q_next))
    eps = 2.0 ** -34
    rows = []
    for t in np.linspace(eps, 1.0 - eps, grid):
        L = lo + float(t) * (hi - lo)
        M = canonical_source_matrix_L(L, N + 1)
        rec = theorem_aligned_pivot_float(M, N, parity)
        rows.append({
            "t": float(t),
            "L": L,
            "H1_predecessor_positive": rec["H1_predecessor_positive"],
            "predecessor_min_eigenvalue": rec["predecessor_min_eigenvalue"],
            "unit_shell_pivot": rec["unit_shell_pivot"],
            "raw_pivot": rec["raw_pivot"],
            "scope": "H1_FIRST_BAD_ALIGNED" if rec["H1_predecessor_positive"] else "OUT_OF_FIRST_BAD_SCOPE",
        })
    h1_rows = [r for r in rows if r["H1_predecessor_positive"]]
    negative_h1 = [r for r in h1_rows if r["unit_shell_pivot"] < 0.0]
    best = min(h1_rows, key=lambda r: r["unit_shell_pivot"]) if h1_rows else None
    return {
        "range": {"from_q": q, "to_next_von_mangoldt_q": q_next, "L_lo": lo, "L_hi": hi},
        "grid": grid,
        "H1_count": len(h1_rows),
        "out_of_scope_count": len(rows) - len(h1_rows),
        "negative_H1_count": len(negative_h1),
        "best_H1_unit_pivot": best,
        "first_negative_H1": negative_h1[0] if negative_h1 else None,
        "rows": rows,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=17)
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--parity", choices=["odd", "even"], default="odd")
    ap.add_argument("--exponents", default="6,8,10,12,14,16,18,20")
    ap.add_argument("--grid", type=int, default=97)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST169_FB05_SCHUR_VISIBILITY_DISCOVERY.json"))
    args = ap.parse_args()
    if args.q < 2 or args.n < 1 or args.grid < 17:
        raise ValueError("require q>=2, n>=1, grid>=17")
    if von_mangoldt_weight_float(args.q) == 0.0:
        raise ValueError("target q must have nonzero von-Mangoldt weight")
    exponents = sorted({int(x) for x in args.exponents.split(",") if x.strip()})
    if not exponents:
        raise ValueError("need source-offset exponents")

    q_next = next_von_mangoldt_threshold(args.q)
    threshold = _background_pivot(args.q, args.n, args.parity, 0.0)
    moment_order, v = moment_vector_step(args.n, args.parity)
    jet_order, kappa = threshold_leading_scalar(args.q, args.parity)
    visibility = schur_visibility_float(threshold["H"], v)
    c2 = float(threshold["geometry"].c2)

    atom_records = []
    for exp in exponents:
        omega = 2.0 ** (-exp)
        rec = pivot_effect_record(args.q, args.n, args.parity, omega)
        residual_scale = omega ** (jet_order + 2)
        rec["unit_residual_over_expected_next_order"] = (
            rec["unit_exact_minus_rank_one"] / residual_scale if residual_scale else None
        )
        atom_records.append(rec)

    finite_differences = [_finite_difference_background(args.q, args.n, args.parity, exp) for exp in exponents if exp >= 8]
    usable = [r for r in finite_differences if r["H1_minus"] and r["H1_zero"] and r["H1_plus"]]
    beta_record = usable[-1] if usable else finite_differences[-1]
    beta = float(beta_record["beta_unit_central_difference"])
    Kkick = float(kappa * visibility["rho2"] / c2)
    omega_next = 1.0 - math.log(float(args.q)) / math.log(float(q_next))
    local_model = _local_model(threshold["unit_shell_pivot"], beta, Kkick, jet_order, omega_next)
    physical = _physical_scout(args.q, q_next, args.n, args.parity, args.grid)

    if not threshold["H1_predecessor_positive"]:
        visibility_class = "OUT_OF_FIRST_BAD_SCOPE"
    elif abs(visibility["rho"]) <= 1e-12 * max(1.0, math.sqrt(c2)):
        visibility_class = "NUMERICALLY_DEGENERATE"
    else:
        visibility_class = "VISIBLE_SIGNAL"

    payload = {
        "schema_version": "POST169_FB05_SCHUR_VISIBILITY_DISCOVERY_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "target": {
            "q": args.q,
            "next_von_mangoldt_q": q_next,
            "N": args.n,
            "Kstar": args.n + 1,
            "parity": args.parity,
            "threshold_L": math.log(float(args.q)),
        },
        "threshold": {
            "H1_predecessor_positive": threshold["H1_predecessor_positive"],
            "predecessor_min_eigenvalue": threshold["predecessor_min_eigenvalue"],
            "raw_pivot": threshold["raw_pivot"],
            "unit_shell_pivot": threshold["unit_shell_pivot"],
            "shell_norm_sq": c2,
            "moment_order": moment_order,
            "jet_order": jet_order,
            "kappa": kappa,
            "rho": visibility["rho"],
            "rho2_over_shell_norm_sq": visibility["rho2"] / c2,
            "gamma": visibility["gamma"],
            "visibility_classification": visibility_class,
        },
        "exact_q_atom_vs_rank_one": atom_records,
        "background_finite_differences": finite_differences,
        "selected_beta_record": beta_record,
        "local_truncated_model": local_model,
        "physical_scout_to_next_von_mangoldt_threshold": physical,
        "interpretation": (
            "The q atom is separated at matrix level before evaluating the nonlinear Schur pivot. "
            "Channel attribution uses the directional derivative of the pivot, not sums of channel pivots."
        ),
        "nonclaims": [
            "Finite differences are not derivative theorems.",
            "A visible threshold direction is not a first-bad contradiction.",
            "No sampled negative pivot implies no whole-interval positivity theorem.",
            "The integer shell generator is ray-equivalent, not magnitude-identical, to Lean's canonical cubic shell.",
            "RH remains OPEN.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "target": payload["target"],
        "threshold": payload["threshold"],
        "selected_beta_record": beta_record,
        "local_truncated_model": local_model,
        "physical_summary": {
            "H1_count": physical["H1_count"],
            "negative_H1_count": physical["negative_H1_count"],
            "best_H1_unit_pivot": physical["best_H1_unit_pivot"],
        },
        "atom_tail": atom_records[-3:],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
