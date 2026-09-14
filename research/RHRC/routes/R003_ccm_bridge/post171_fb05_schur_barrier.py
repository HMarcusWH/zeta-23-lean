#!/usr/bin/env python3
"""Threshold-to-threshold Schur barrier utilities for post-#171 FB-05 work.

This module reuses the theorem-aligned one-step Schur geometry established by
PR #170.  The primary scalar is the unit-shell pivot in the exact [W|c]
predecessor/shell geometry.  A genuine arithmetic cell starts at an integer q
with nonzero von-Mangoldt weight and ends at the next such integer q_next.

For omega = 1 - log(q)/L in [0, omega_next], the current-q atom starts at zero
and accumulates across the cell.  We therefore separate

    P_full(omega) = P_bg(omega) + A_q(omega),

where A_q is the *exact nonlinear Schur lift* produced by adding the signed
q-atom to the same background matrix.  Channel attribution is performed only
through the directional Schur derivative; channel pivots are never added.

Floating results are discovery/audit data only.  RH remains OPEN.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.optimize import minimize_scalar

from post167_fb05_threshold_jet import von_mangoldt_weight_float
from post169_fb05_schur_visibility import (
    background_signed_channels_at_omega_float,
    directional_schur_derivative_float,
    full_background_at_omega_float,
    restricted_step_matrix_float,
    theorem_aligned_pivot_float,
)


@dataclass(frozen=True)
class ArithmeticCell:
    q: int
    q_next: int
    L_start: float
    L_end: float
    omega_end: float


def next_von_mangoldt_threshold(q: int) -> int:
    if q < 2 or von_mangoldt_weight_float(q) == 0.0:
        raise ValueError("q must have nonzero von-Mangoldt weight")
    for k in range(q + 1, q + 100000):
        if von_mangoldt_weight_float(k) != 0.0:
            return k
    raise ArithmeticError("failed to find next nonzero von-Mangoldt threshold")


def arithmetic_cell(q: int) -> ArithmeticCell:
    q_next = next_von_mangoldt_threshold(q)
    L0 = math.log(float(q))
    L1 = math.log(float(q_next))
    omega1 = 1.0 - L0 / L1
    if not (0.0 < omega1 < 1.0):
        raise AssertionError("invalid arithmetic-cell source-coordinate endpoint")
    return ArithmeticCell(q=q, q_next=q_next, L_start=L0, L_end=L1, omega_end=omega1)


def omega_to_L(q: int, omega: float) -> float:
    if q < 2 or not (0.0 <= omega < 1.0):
        raise ValueError("require q>=2 and 0<=omega<1")
    return math.log(float(q)) / (1.0 - float(omega))


def L_to_omega(q: int, L: float) -> float:
    if q < 2 or L < math.log(float(q)):
        raise ValueError("L must be at or to the right of log(q)")
    return 1.0 - math.log(float(q)) / float(L)


def barrier_point(q: int, predecessor_N: int, parity: str, omega: float) -> dict:
    cell = arithmetic_cell(q)
    if not (0.0 <= omega <= cell.omega_end):
        raise ValueError("omega outside arithmetic cell")
    state = full_background_at_omega_float(q, predecessor_N, float(omega))
    full = theorem_aligned_pivot_float(state["full"], predecessor_N, parity)
    bg = theorem_aligned_pivot_float(state["background"], predecessor_N, parity)
    c2 = float(full["geometry"].c2)
    lift_raw = float(full["raw_pivot"] - bg["raw_pivot"])
    return {
        "q": q,
        "q_next": cell.q_next,
        "N": predecessor_N,
        "Kstar": predecessor_N + 1,
        "parity": parity,
        "omega": float(omega),
        "L": float(state["L"]),
        "H1_full": bool(full["H1_predecessor_positive"]),
        "H1_background": bool(bg["H1_predecessor_positive"]),
        "full_predecessor_min_eigenvalue": full["predecessor_min_eigenvalue"],
        "background_predecessor_min_eigenvalue": bg["predecessor_min_eigenvalue"],
        "raw_full_pivot": float(full["raw_pivot"]),
        "unit_full_pivot": float(full["unit_shell_pivot"]),
        "raw_background_pivot": float(bg["raw_pivot"]),
        "unit_background_pivot": float(bg["unit_shell_pivot"]),
        "raw_exact_entry_lift": lift_raw,
        "unit_exact_entry_lift": lift_raw / c2,
        "scope": "H1_FIRST_BAD_ALIGNED" if full["H1_predecessor_positive"] else "OUT_OF_FIRST_BAD_SCOPE",
    }


def direct_cell_budget(q: int, predecessor_N: int, parity: str) -> dict:
    cell = arithmetic_cell(q)
    start = barrier_point(q, predecessor_N, parity, 0.0)
    end = barrier_point(q, predecessor_N, parity, cell.omega_end)
    full_change = end["unit_full_pivot"] - start["unit_full_pivot"]
    bg_change = end["unit_background_pivot"] - start["unit_background_pivot"]
    lift = end["unit_exact_entry_lift"]
    return {
        "cell": {
            "q": q,
            "q_next": cell.q_next,
            "L_start": cell.L_start,
            "L_end": cell.L_end,
            "omega_end": cell.omega_end,
        },
        "start": start,
        "end": end,
        "unit_full_endpoint_change": full_change,
        "unit_background_endpoint_change": bg_change,
        "unit_entry_lift_at_end": lift,
        "unit_cell_budget_reconstruction_error": full_change - (bg_change + lift),
    }


def _objective(q: int, N: int, parity: str, background: bool, omega: float) -> float:
    rec = barrier_point(q, N, parity, omega)
    h1 = rec["H1_background"] if background else rec["H1_full"]
    if not h1:
        return 1e100
    return rec["unit_background_pivot"] if background else rec["unit_full_pivot"]


def find_pivot_minimum(
    q: int,
    predecessor_N: int,
    parity: str,
    *,
    background: bool = False,
    grid: int = 129,
    local_seeds: int = 8,
) -> dict:
    if grid < 17 or local_seeds < 1:
        raise ValueError("require grid>=17 and local_seeds>=1")
    cell = arithmetic_cell(q)
    omegas = np.linspace(0.0, cell.omega_end, grid)
    rows = [barrier_point(q, predecessor_N, parity, float(w)) for w in omegas]
    key = "unit_background_pivot" if background else "unit_full_pivot"
    h1_key = "H1_background" if background else "H1_full"
    h1_rows = [r for r in rows if r[h1_key]]
    h1_lost = len(h1_rows) != len(rows)
    if not h1_rows:
        return {
            "available": False,
            "background": background,
            "H1_lost_on_grid": True,
            "grid_rows": rows,
            "best": None,
        }

    order = sorted(range(len(rows)), key=lambda i: rows[i][key] if rows[i][h1_key] else 1e100)
    candidates = [rows[order[0]]]
    used: set[tuple[int, int]] = set()
    for idx in order[: max(local_seeds * 2, local_seeds)]:
        if len(candidates) >= local_seeds + 1:
            break
        if idx <= 0 or idx >= len(rows) - 1:
            continue
        if not (rows[idx - 1][h1_key] and rows[idx][h1_key] and rows[idx + 1][h1_key]):
            continue
        pair = (idx - 1, idx + 1)
        if pair in used:
            continue
        used.add(pair)
        lo = float(omegas[idx - 1])
        hi = float(omegas[idx + 1])
        res = minimize_scalar(
            lambda w: _objective(q, predecessor_N, parity, background, float(w)),
            bounds=(lo, hi),
            method="bounded",
            options={"xatol": 2e-14, "maxiter": 200},
        )
        if res.success and math.isfinite(float(res.fun)):
            candidates.append(barrier_point(q, predecessor_N, parity, float(res.x)))

    best = min(candidates, key=lambda r: r[key])
    return {
        "available": True,
        "background": background,
        "H1_lost_on_grid": h1_lost,
        "grid_H1_count": len(h1_rows),
        "grid_count": len(rows),
        "best": best,
        "grid_rows": rows,
    }


def _channel_direction_at(
    q: int,
    predecessor_N: int,
    parity: str,
    omega: float,
    h: float,
) -> dict:
    cell = arithmetic_cell(q)
    if not (0.0 < omega < cell.omega_end):
        raise ValueError("direction point must be interior")
    h = min(float(h), 0.24 * omega, 0.24 * (cell.omega_end - omega))
    if not h > 0.0:
        raise ValueError("invalid derivative stencil")

    center_state = full_background_at_omega_float(q, predecessor_N, omega)
    center = theorem_aligned_pivot_float(center_state["background"], predecessor_N, parity)
    if not center["H1_predecessor_positive"]:
        return {"available": False, "H1_background": False, "omega": omega, "h": h}

    minus = background_signed_channels_at_omega_float(q, predecessor_N, omega - h)
    plus = background_signed_channels_at_omega_float(q, predecessor_N, omega + h)
    c2 = float(center["geometry"].c2)
    contrib: dict[str, float] = {}
    total_D = np.zeros_like(center["H"])
    for name in ("pole", "arch_signed", "prime_signed", "scalar_shift"):
        Hm = restricted_step_matrix_float(minus[name], center["geometry"])
        Hp = restricted_step_matrix_float(plus[name], center["geometry"])
        D = (Hp - Hm) / (2.0 * h)
        total_D += D
        contrib[name] = directional_schur_derivative_float(center["H"], D) / c2
    total = directional_schur_derivative_float(center["H"], total_D) / c2
    return {
        "available": True,
        "H1_background": True,
        "omega": omega,
        "h": h,
        "channel_directional_contributions": contrib,
        "channel_sum": float(sum(contrib.values())),
        "directional_total": float(total),
        "channel_sum_minus_total": float(sum(contrib.values()) - total),
    }


def integrate_background_channels(
    q: int,
    predecessor_N: int,
    parity: str,
    *,
    nodes: int = 12,
    stencil_fraction: float = 2e-5,
) -> dict:
    if nodes < 4:
        raise ValueError("require at least four Gauss-Legendre nodes")
    cell = arithmetic_cell(q)
    xs, ws = leggauss(nodes)
    omegas = 0.5 * cell.omega_end * (xs + 1.0)
    weights = 0.5 * cell.omega_end * ws
    h0 = max(stencil_fraction * cell.omega_end, 1e-9)

    totals = {name: 0.0 for name in ("pole", "arch_signed", "prime_signed", "scalar_shift")}
    directional_total = 0.0
    records = []
    for omega, weight in zip(omegas, weights):
        rec = _channel_direction_at(q, predecessor_N, parity, float(omega), h0)
        records.append(rec)
        if not rec["available"]:
            return {
                "available": False,
                "reason": "H1_SCOPE_LOST_AT_QUADRATURE_NODE",
                "records": records,
            }
        for name in totals:
            totals[name] += float(weight) * rec["channel_directional_contributions"][name]
        directional_total += float(weight) * rec["directional_total"]

    budget = direct_cell_budget(q, predecessor_N, parity)
    direct_bg_change = float(budget["unit_background_endpoint_change"])
    channel_sum = float(sum(totals.values()))
    cancellation_den = max(abs(channel_sum), 1e-300)
    cancellation_ratio = float(sum(abs(v) for v in totals.values()) / cancellation_den)
    return {
        "available": True,
        "nodes": nodes,
        "stencil_fraction": stencil_fraction,
        "channel_integrals": totals,
        "channel_integral_sum": channel_sum,
        "integrated_directional_total": float(directional_total),
        "direct_background_endpoint_change": direct_bg_change,
        "channel_sum_minus_direct_change": channel_sum - direct_bg_change,
        "directional_total_minus_direct_change": directional_total - direct_bg_change,
        "cancellation_ratio": cancellation_ratio,
        "records": records,
        "claim_cap": "FLOATING_ENVELOPE_INTEGRATION_DIAGNOSTIC_ONLY",
    }


def barrier_case(
    q: int,
    predecessor_N: int,
    parity: str,
    *,
    grid: int = 129,
    local_seeds: int = 8,
    integration_nodes: int = 12,
) -> dict:
    budget = direct_cell_budget(q, predecessor_N, parity)
    full_min = find_pivot_minimum(q, predecessor_N, parity, background=False, grid=grid, local_seeds=local_seeds)
    bg_min = find_pivot_minimum(q, predecessor_N, parity, background=True, grid=grid, local_seeds=local_seeds)
    integration = integrate_background_channels(q, predecessor_N, parity, nodes=integration_nodes)

    start = budget["start"]
    if not start["H1_full"]:
        classification = "H1_SCOPE_LOST"
    elif full_min["best"] is None:
        classification = "NUMERICALLY_UNRESOLVED"
    elif full_min["best"]["unit_full_pivot"] < 0.0:
        # A negative pivot at an H1-aligned point is the highest-value finite
        # discovery even if H1 is lost elsewhere in the same arithmetic cell.
        classification = "SAMPLED_BAD_SUCCESSOR"
    elif full_min["H1_lost_on_grid"]:
        classification = "H1_SCOPE_LOST"
    else:
        classification = "SAMPLED_BARRIER_SURVIVES"

    P0 = float(start["unit_full_pivot"])
    best_full = full_min["best"]
    best_bg = bg_min["best"]
    lift_at_danger = None if best_full is None else barrier_point(
        q, predecessor_N, parity, float(best_full["omega"])
    )["unit_exact_entry_lift"]
    headroom_ratio = None if best_full is None or P0 == 0.0 else float(best_full["unit_full_pivot"] / P0)
    background_drawdown = None if best_bg is None else float(P0 - best_bg["unit_background_pivot"])

    return {
        "target": {"q": q, "q_next": budget["cell"]["q_next"], "N": predecessor_N, "Kstar": predecessor_N + 1, "parity": parity},
        "classification": classification,
        "direct_cell_budget": budget,
        "physical_minimum": full_min,
        "background_minimum": bg_min,
        "unit_entry_lift_at_physical_minimum": lift_at_danger,
        "unit_background_drawdown_to_background_minimum": background_drawdown,
        "headroom_ratio": headroom_ratio,
        "background_channel_integration": integration,
        "claim_cap": "EXPERIMENTAL_THRESHOLD_TO_THRESHOLD_BARRIER_AUDIT_ONLY",
    }
