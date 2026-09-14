#!/usr/bin/env python3
"""Theorem-aligned one-step Schur visibility utilities for post-#169 FB-05 work.

The scalar object here is the zero-shift one-step Schur pivot in the exact
centered predecessor / intrinsic-shell geometry

    B_step = [W | c],
    H = B_step^T M B_step = [[A,b],[b^T,d]],
    P = d - b^T A^{-1} b.

`c` is the checked-in exact integer shell generator. It spans the same
one-dimensional shell as Lean's `intrinsicCubicShellPart`, but is not asserted
to have the same magnitude. Raw pivots are therefore reported together with
the scale-invariant unit-shell normalization P / ||c||^2.

All results in this module are research/audit tooling only. RH remains OPEN.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
import sympy as sp

from canonical_source_numeric import canonical_source_matrix_L, signed_channel_matrices_L
from post150_selected_residual import centered_predecessor_basis, exact_shell_generator, sympy_to_numpy
from post167_fb05_threshold_jet import (
    aperture_from_source_coordinate,
    canonical_entering_atom_float,
    centered_moment_row,
    von_mangoldt_weight_float,
)


@dataclass(frozen=True)
class OneStepGeometry:
    predecessor_N: int
    parity: str
    W_exact: sp.Matrix
    c_exact: sp.Matrix
    step_basis_exact: sp.Matrix
    c2: int


def one_step_geometry(predecessor_N: int, parity: str) -> OneStepGeometry:
    if predecessor_N < 1:
        raise ValueError("require predecessor_N>=1")
    if parity not in ("even", "odd"):
        raise ValueError("parity must be even or odd")
    W = centered_predecessor_basis(predecessor_N, parity)
    c = exact_shell_generator(predecessor_N, parity)
    if W.T * c != sp.zeros(W.cols, 1):
        raise AssertionError("shell generator is not orthogonal to centered predecessor")
    B = sp.Matrix.hstack(W, c)
    c2 = int((c.T * c)[0, 0])
    if c2 <= 0:
        raise AssertionError("shell generator has nonpositive squared norm")
    return OneStepGeometry(predecessor_N, parity, W, c, B, c2)


def restricted_step_matrix_float(M: np.ndarray, geom: OneStepGeometry) -> np.ndarray:
    B = sympy_to_numpy(geom.step_basis_exact)
    return B.T @ np.asarray(M, dtype=float) @ B


def schur_blocks_float(H: np.ndarray) -> tuple[np.ndarray, np.ndarray, float]:
    H = np.asarray(H, dtype=float)
    if H.ndim != 2 or H.shape[0] != H.shape[1] or H.shape[0] < 1:
        raise ValueError("expected nonempty square one-step matrix")
    if H.shape[0] == 1:
        return np.zeros((0, 0), dtype=float), np.zeros(0, dtype=float), float(H[0, 0])
    return H[:-1, :-1], H[:-1, -1], float(H[-1, -1])


def predecessor_positive_float(A: np.ndarray, rel_tol: float = 2e-12) -> tuple[bool, float | None]:
    if A.size == 0:
        return True, None
    As = (A + A.T) / 2.0
    vals = np.linalg.eigvalsh(As)
    mineig = float(vals[0])
    scale = max(float(np.linalg.norm(As, 2)), 1.0)
    return bool(mineig > rel_tol * scale), mineig


def schur_pivot_float(H: np.ndarray) -> dict:
    A, b, d = schur_blocks_float(H)
    if A.size:
        x = np.linalg.solve(A, b)
        correction = float(b @ x)
    else:
        x = np.zeros(0, dtype=float)
        correction = 0.0
    pivot = float(d - correction)
    return {"A": A, "b": b, "d": d, "x": x, "pivot": pivot, "correction": correction}


def theorem_aligned_pivot_float(M: np.ndarray, predecessor_N: int, parity: str) -> dict:
    geom = one_step_geometry(predecessor_N, parity)
    H = restricted_step_matrix_float(M, geom)
    blocks = schur_pivot_float(H)
    h1, predecessor_min = predecessor_positive_float(blocks["A"])
    return {
        "geometry": geom,
        "H": H,
        **blocks,
        "H1_predecessor_positive": h1,
        "predecessor_min_eigenvalue": predecessor_min,
        "raw_pivot": blocks["pivot"],
        "unit_shell_pivot": blocks["pivot"] / float(geom.c2),
    }


def moment_vector_step(predecessor_N: int, parity: str) -> tuple[int, np.ndarray]:
    geom = one_step_geometry(predecessor_N, parity)
    K = predecessor_N + 1
    moment_order = 3 if parity == "odd" else 4 if parity == "even" else None
    if moment_order is None:
        raise ValueError("parity must be even or odd")
    row = centered_moment_row(K, geom.step_basis_exact, moment_order)
    return moment_order, np.asarray(row, dtype=float).reshape(-1)


def threshold_leading_scalar(q: int, parity: str) -> tuple[int, float]:
    weight = von_mangoldt_weight_float(q)
    if weight == 0.0:
        raise ValueError("q has zero von-Mangoldt weight")
    if parity == "odd":
        return 7, weight * 2.0 * (2.0 * math.pi) ** 6 / math.factorial(7)
    if parity == "even":
        return 9, -weight * 2.0 * (2.0 * math.pi) ** 8 / math.factorial(9)
    raise ValueError("parity must be even or odd")


def schur_visibility_float(H_background: np.ndarray, v: np.ndarray) -> dict:
    blocks = schur_pivot_float(H_background)
    A = blocks["A"]
    v = np.asarray(v, dtype=float).reshape(-1)
    if len(v) != H_background.shape[0]:
        raise ValueError("visibility vector dimension mismatch")
    a = v[:-1]
    alpha = float(v[-1])
    if A.size:
        x = blocks["x"]
        z = np.linalg.solve(A, a)
        rho = float(alpha - a @ x)
        gamma = float(a @ z)
    else:
        rho = alpha
        gamma = 0.0
    return {"rho": rho, "rho2": rho * rho, "gamma": gamma, "a": a, "alpha": alpha}


def rank_one_pivot_effect_float(tau: float, rho: float, gamma: float) -> float:
    den = 1.0 + float(tau) * float(gamma)
    if abs(den) < 1e-15:
        raise ArithmeticError("rank-one Schur denominator is numerically singular")
    return float(float(tau) * float(rho) ** 2 / den)


def rank_one_pivot_update_float(pivot: float, tau: float, rho: float, gamma: float) -> float:
    return float(pivot + rank_one_pivot_effect_float(tau, rho, gamma))


def directional_schur_derivative_float(H: np.ndarray, D: np.ndarray) -> float:
    blocks = schur_pivot_float(H)
    DA, Db, Dd = schur_blocks_float(np.asarray(D, dtype=float))
    x = blocks["x"]
    if DA.size:
        return float(Dd - 2.0 * Db @ x + x @ DA @ x)
    return float(Dd)


def signed_entering_atom_float(q: int, predecessor_N: int, omega: float) -> np.ndarray:
    return canonical_entering_atom_float(q, predecessor_N + 1, omega)


def full_background_at_omega_float(q: int, predecessor_N: int, omega: float) -> dict:
    L = aperture_from_source_coordinate(q, float(omega))
    K = predecessor_N + 1
    full = canonical_source_matrix_L(L, K)
    atom = signed_entering_atom_float(q, predecessor_N, float(omega))
    background = full - atom if omega > 0.0 else full.copy()
    return {"L": L, "full": full, "background": background, "signed_q_atom": atom}


def background_signed_channels_at_omega_float(q: int, predecessor_N: int, omega: float) -> dict[str, np.ndarray]:
    L = aperture_from_source_coordinate(q, float(omega))
    K = predecessor_N + 1
    channels = {k: v.copy() for k, v in signed_channel_matrices_L(L, K).items()}
    if omega > 0.0:
        channels["prime_signed"] = channels["prime_signed"] - signed_entering_atom_float(q, predecessor_N, omega)
    return channels


def pivot_effect_record(q: int, predecessor_N: int, parity: str, omega: float) -> dict:
    state = full_background_at_omega_float(q, predecessor_N, omega)
    full_rec = theorem_aligned_pivot_float(state["full"], predecessor_N, parity)
    bg_rec = theorem_aligned_pivot_float(state["background"], predecessor_N, parity)
    moment_order, v = moment_vector_step(predecessor_N, parity)
    jet_order, kappa = threshold_leading_scalar(q, parity)
    if 2 * moment_order + 1 != jet_order:
        raise AssertionError("moment/jet order mismatch")
    vis = schur_visibility_float(bg_rec["H"], v)
    tau = kappa * float(omega) ** jet_order
    model_effect = rank_one_pivot_effect_float(tau, vis["rho"], vis["gamma"])
    exact_effect = full_rec["raw_pivot"] - bg_rec["raw_pivot"]
    c2 = float(bg_rec["geometry"].c2)

    # The production matrix builder is ordinary double-precision discovery
    # arithmetic. Once the predicted effect is below this relative floor, a
    # subtraction of two near-equal Schur pivots is deliberately not treated as
    # asymptotic evidence. Arb replay is the authority for those points.
    resolution_floor = 1e-8 * max(abs(bg_rec["raw_pivot"]), 1e-30)
    resolved = abs(model_effect) >= resolution_floor
    residual = exact_effect - model_effect if resolved else None

    return {
        "L": state["L"],
        "omega": float(omega),
        "H1_background": bg_rec["H1_predecessor_positive"],
        "H1_full": full_rec["H1_predecessor_positive"],
        "raw_background_pivot": bg_rec["raw_pivot"],
        "unit_background_pivot": bg_rec["unit_shell_pivot"],
        "raw_full_pivot": full_rec["raw_pivot"],
        "unit_full_pivot": full_rec["unit_shell_pivot"],
        "raw_exact_q_pivot_effect": exact_effect,
        "unit_exact_q_pivot_effect": exact_effect / c2,
        "raw_rank_one_model_effect": model_effect,
        "unit_rank_one_model_effect": model_effect / c2,
        "raw_exact_minus_rank_one": residual,
        "unit_exact_minus_rank_one": None if residual is None else residual / c2,
        "float_exact_effect_resolved": resolved,
        "float_resolution_floor": resolution_floor,
        "jet_order": jet_order,
        "kappa": kappa,
        "rho": vis["rho"],
        "rho2_over_c2": vis["rho2"] / c2,
        "gamma": vis["gamma"],
        "tau": tau,
        "first_bad_scope": "H1_FIRST_BAD_ALIGNED" if bg_rec["H1_predecessor_positive"] else "OUT_OF_FIRST_BAD_SCOPE",
    }
