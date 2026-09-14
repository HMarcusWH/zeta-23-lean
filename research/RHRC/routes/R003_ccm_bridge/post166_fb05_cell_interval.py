#!/usr/bin/env python3
"""Fixed-cell determinant barrier utilities for the post-#166 FB-05 audit.

The primary target is the near-critical odd successor discovered after PR #166:

    Q = 16, predecessor N = 3, successor K = 4, odd parity.

Floating arithmetic is used only for discovery.  Rigorous interval work uses a
fixed-Q continuation of the production canonical source matrix.  On the closed
cell log(Q) <= L <= log(Q+1), keeping the Q-truncated prime sum is legitimate as
a continuous extension: a prime-power atom entering at a threshold has
q_basis(..., y=L, L)=0.  This lets an Arb interval cover the physical cutoff
cell including its endpoints without silently leaving untested tails.

No interval result produced here is Lean theorem authority.  RH remains OPEN.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
import sympy as sp
from flint import arb, arb_mat

from canonical_source_arb import (
    alpha_L,
    ball_record,
    beta_L,
    definitely_negative,
    definitely_positive,
    direct_arch_component,
    pole_component,
    prime_component,
    source_eq44_gamma_L,
)
from canonical_source_numeric import canonical_source_matrix_L, fixed_cell_bounds
from post150_selected_residual import exact_parity_basis, orthonormal_columns, sympy_to_numpy


@dataclass(frozen=True)
class CellTarget:
    Q: int
    predecessor_N: int
    parity: str

    @property
    def Kstar(self) -> int:
        return self.predecessor_N + 1


def cell_coordinate_L(Q: int, t: float) -> float:
    if Q < 1:
        raise ValueError("require Q>=1")
    if not 0.0 <= t <= 1.0:
        raise ValueError("require 0<=t<=1")
    lo, hi = fixed_cell_bounds(Q)
    return lo + float(t) * (hi - lo)


def _raw_restriction_float(M: np.ndarray, B: sp.Matrix) -> np.ndarray:
    if B.cols == 0:
        return np.zeros((0, 0), dtype=float)
    X = sympy_to_numpy(B)
    return X.T @ M @ X


def _principal_determinants_float(H: np.ndarray) -> list[float]:
    return [float(np.linalg.det(H[:k, :k])) for k in range(1, H.shape[0] + 1)]


def successor_barrier_float(Q: int, predecessor_N: int, parity: str, t: float) -> dict:
    """Discovery diagnostics for one point of a fixed physical cutoff cell."""
    if parity not in ("even", "odd"):
        raise ValueError("parity must be even or odd")
    K = predecessor_N + 1
    L = cell_coordinate_L(Q, t)
    M = canonical_source_matrix_L(L, K)
    B = exact_parity_basis(K, parity)
    Hraw = _raw_restriction_float(M, B)
    Qb = orthonormal_columns(B)
    H = Qb.T @ M @ Qb if B.cols else np.zeros((0, 0), dtype=float)
    if H.size:
        Hs = (H + H.T) / 2.0
        eigs = np.linalg.eigvalsh(Hs)
        mineig = float(eigs[0])
        maxeig = float(eigs[-1])
        spectral_scale = max(float(np.linalg.norm(Hs, 2)), 1e-300)
        normalized_min = mineig / spectral_scale
        normalized_det = float(np.linalg.det(Hs)) / (spectral_scale ** H.shape[0])
        condition_ratio = mineig / max(abs(maxeig), 1e-300)
    else:
        eigs = np.array([], dtype=float)
        mineig = math.inf
        maxeig = math.inf
        spectral_scale = 1.0
        normalized_min = math.inf
        normalized_det = 1.0
        condition_ratio = math.inf
    return {
        "Q": int(Q),
        "N": int(predecessor_N),
        "Kstar": int(K),
        "parity": parity,
        "t": float(t),
        "L": float(L),
        "dimension": int(B.cols),
        "min_eigenvalue": mineig if math.isfinite(mineig) else None,
        "max_eigenvalue": maxeig if math.isfinite(maxeig) else None,
        "spectral_scale": spectral_scale,
        "normalized_min_eigenvalue": normalized_min if math.isfinite(normalized_min) else None,
        "condition_ratio": condition_ratio if math.isfinite(condition_ratio) else None,
        "raw_leading_principal_determinants": _principal_determinants_float(Hraw),
        "orthonormal_normalized_determinant": normalized_det,
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
    }


def _arb_matrix_from_sympy(A: sp.Matrix) -> arb_mat:
    if A.cols == 0:
        return arb_mat(A.rows, 0)
    return arb_mat([[int(A[r, c]) for c in range(A.cols)] for r in range(A.rows)])


def _arb_leading_block(H: arb_mat, k: int) -> arb_mat:
    return arb_mat([[H[r, c] for c in range(k)] for r in range(k)])


def principal_determinants_arb(H: arb_mat) -> list[arb]:
    return [_arb_leading_block(H, k).det() for k in range(1, H.nrows() + 1)]


def fixed_q_canonical_source_matrix_arb(L: arb, N: int, Q: int) -> arb_mat:
    """Production canonical source with a fixed prime cutoff Q.

    Unlike canonical_source_arb.canonical_source_matrix, this helper deliberately
    does not demand strict interior fixed-cell membership.  It is used only on
    L-balls contained in the closed cell [log Q, log(Q+1)].  The Q-truncated
    formula is the continuous one-sided extension at both thresholds because
    the entering threshold atom vanishes at y=L.
    """
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")
    idx = list(range(-N, N + 1))
    alpha_cache = {n: alpha_L(n, L) for n in idx}
    beta_cache = {n: beta_L(n, L) for n in idx}
    gamma_cache = {n: source_eq44_gamma_L(n, L) for n in idx}
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            value = (
                pole_component(n, m, L)
                - direct_arch_component(n, m, L, alpha_cache, beta_cache, gamma_cache)
                - prime_component(n, m, L, Q)
            )
            rows[r][c] = value
            rows[c][r] = value
    return arb_mat(rows)


def arb_unit_interval(lo_num: int, hi_num: int, den: int) -> arb:
    if den <= 0 or not 0 <= lo_num < hi_num <= den:
        raise ValueError("require 0 <= lo < hi <= den")
    mid_num = lo_num + hi_num
    mid_den = 2 * den
    rad_num = hi_num - lo_num
    rad_den = 2 * den
    return arb(f"{mid_num}/{mid_den}", f"{rad_num}/{rad_den}")


def cell_coordinate_L_arb(Q: int, t: arb) -> arb:
    if Q < 1:
        raise ValueError("require Q>=1")
    lo = arb(Q).log()
    hi = arb(Q + 1).log()
    return lo + t * (hi - lo)


def successor_restriction_arb(Q: int, predecessor_N: int, parity: str, t: arb) -> tuple[arb, arb_mat]:
    if parity not in ("even", "odd"):
        raise ValueError("parity must be even or odd")
    K = predecessor_N + 1
    L = cell_coordinate_L_arb(Q, t)
    M = fixed_q_canonical_source_matrix_arb(L, K, Q)
    B = exact_parity_basis(K, parity)
    Bb = _arb_matrix_from_sympy(B)
    H = Bb.transpose() * M * Bb if B.cols else arb_mat(0, 0)
    return L, H


def classify_principal_minors(minors: list[arb]) -> str:
    if all(definitely_positive(x) for x in minors):
        return "POSITIVE_CERTIFIED"
    if any(definitely_negative(x) for x in minors):
        return "BAD_INTERVAL_CERTIFIED"
    return "UNRESOLVED"


def certify_dyadic_cell_interval(
    Q: int,
    predecessor_N: int,
    parity: str,
    lo_num: int,
    hi_num: int,
    den: int,
) -> dict:
    """Rigorous Sylvester classification on one dyadic t interval."""
    t = arb_unit_interval(lo_num, hi_num, den)
    try:
        L, H = successor_restriction_arb(Q, predecessor_N, parity, t)
        minors = principal_determinants_arb(H)
        classification = classify_principal_minors(minors)
        return {
            "Q": Q,
            "N": predecessor_N,
            "Kstar": predecessor_N + 1,
            "parity": parity,
            "t_interval": {
                "lo_num": lo_num,
                "hi_num": hi_num,
                "den": den,
                "ball": ball_record(t),
            },
            "L_ball": ball_record(L),
            "classification": classification,
            "leading_principal_minors": [ball_record(x) for x in minors],
            "exception": None,
        }
    except Exception as exc:
        return {
            "Q": Q,
            "N": predecessor_N,
            "Kstar": predecessor_N + 1,
            "parity": parity,
            "t_interval": {"lo_num": lo_num, "hi_num": hi_num, "den": den},
            "classification": "UNRESOLVED",
            "leading_principal_minors": [],
            "exception": repr(exc),
        }


def adaptive_cell_cover(
    Q: int,
    predecessor_N: int,
    parity: str,
    max_depth: int = 5,
) -> dict:
    """Adaptively classify the entire t in [0,1] cutoff cell.

    An unresolved parent is bisected.  Positive or bad intervals are terminal.
    Failure to certify is retained as UNRESOLVED and is never interpreted as a
    sign change.
    """
    if max_depth < 0:
        raise ValueError("max_depth must be nonnegative")
    stack: list[tuple[int, int, int, int]] = [(0, 1, 1, 0)]
    leaves: list[dict] = []
    while stack:
        lo_num, hi_num, den, depth = stack.pop()
        rec = certify_dyadic_cell_interval(Q, predecessor_N, parity, lo_num, hi_num, den)
        rec["depth"] = depth
        if rec["classification"] != "UNRESOLVED" or depth >= max_depth:
            leaves.append(rec)
            continue
        # Convert [lo/den, hi/den] to two children with common denominator 2*den.
        left_lo = 2 * lo_num
        mid = lo_num + hi_num
        right_hi = 2 * hi_num
        child_den = 2 * den
        stack.append((mid, right_hi, child_den, depth + 1))
        stack.append((left_lo, mid, child_den, depth + 1))

    widths = {"POSITIVE_CERTIFIED": 0.0, "BAD_INTERVAL_CERTIFIED": 0.0, "UNRESOLVED": 0.0}
    counts = {k: 0 for k in widths}
    for rec in leaves:
        t_rec = rec["t_interval"]
        width = (int(t_rec["hi_num"]) - int(t_rec["lo_num"])) / int(t_rec["den"])
        widths[rec["classification"]] += width
        counts[rec["classification"]] += 1
    return {
        "Q": Q,
        "N": predecessor_N,
        "Kstar": predecessor_N + 1,
        "parity": parity,
        "max_depth": max_depth,
        "leaf_count": len(leaves),
        "counts": counts,
        "coverage_fraction": widths,
        "whole_cell_positive_certified": widths["POSITIVE_CERTIFIED"] == 1.0,
        "bad_interval_found": widths["BAD_INTERVAL_CERTIFIED"] > 0.0,
        "leaves": leaves,
        "claim_cap": "RIGOROUS_FINITE_INTERVAL_AUDIT_ONLY",
    }
