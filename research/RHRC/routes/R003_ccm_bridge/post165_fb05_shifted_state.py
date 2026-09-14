#!/usr/bin/env python3
"""Post-#165 same-state FB-05 discriminator on the actual shifted secular ray.

This module extends the post-#150 finite geometry without mutating it.  The old
selected-residual tool constructs the zero-shift Schur trial.  The #161/#163
retained first-bad theorems instead use the negative-root shifted secular trial.
For an exact predecessor basis W, shell generator c, and production canonical
source matrix M, the correct coordinate system is

    H = W^T M W,
    G = W^T W,
    r = W^T M c,

and the shifted trial is

    u_lam = c - W (H - lam G)^(-1) r.

The Gram factor G is essential because the checked-in integer predecessor basis
is not orthonormal.  Replacing H-lam G by H-lam I would not implement the Lean
resolvent construction.

All floating results in this file are discovery diagnostics only.  Rigorous
finite replay lives in ``certify_post165_fb05_same_state_scope.py``.  Nothing in
this module has theorem or RH-promotion authority.
"""
from __future__ import annotations

import math
from typing import Literal

import mpmath as mp
import numpy as np
from scipy.optimize import brentq

from canonical_riesz_endpoint_scalar import canonical_riesz_endpoint_scalar_mp
from canonical_source_numeric import (
    canonical_source_matrix_L,
    signed_channel_matrices_L,
)
from post150_selected_residual import (
    centered_predecessor_basis,
    evaluate_selected_residual_state,
    exact_parity_basis,
    exact_shell_generator,
    integer_direction_from_float,
    orthonormal_columns,
    sympy_to_numpy,
)

Parity = Literal["even", "odd"]


def shifted_predecessor_system(
    M: np.ndarray,
    W_exact,
    c_exact,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float, float]:
    """Return (H,G,r,q,c2) for the exact integer predecessor/shell geometry."""
    W = sympy_to_numpy(W_exact)
    c = sympy_to_numpy(c_exact).reshape(-1)
    H = W.T @ M @ W if W_exact.cols else np.zeros((0, 0), dtype=float)
    G = W.T @ W if W_exact.cols else np.zeros((0, 0), dtype=float)
    r = W.T @ M @ c if W_exact.cols else np.zeros(0, dtype=float)
    q = float(c @ M @ c)
    c2 = float(c @ c)
    return H, G, r, q, c2


def shifted_secular_scalar(
    lam: float,
    H: np.ndarray,
    G: np.ndarray,
    r: np.ndarray,
    q: float,
    c2: float,
) -> float:
    """Shell residual scalar with the same zero set as Lean's quotient scalar."""
    if H.size:
        x = np.linalg.solve(H - float(lam) * G, r)
        correction = float(r @ x)
    else:
        correction = 0.0
    return float(q - float(lam) * c2 - correction)


def shifted_trial_vector(
    lam: float,
    M: np.ndarray,
    W_exact,
    c_exact,
) -> tuple[np.ndarray, dict]:
    """Construct c-W(H-lam G)^(-1)r and return its algebra diagnostics."""
    W = sympy_to_numpy(W_exact)
    c = sympy_to_numpy(c_exact).reshape(-1)
    H, G, r, q, c2 = shifted_predecessor_system(M, W_exact, c_exact)
    if H.size:
        x = np.linalg.solve(H - float(lam) * G, r)
        u = c - W @ x
    else:
        x = np.zeros(0, dtype=float)
        u = c.copy()
    residual = M @ u - float(lam) * u
    predecessor_residual = W.T @ residual if W_exact.cols else np.zeros(0)
    shell_residual = float(c @ residual)
    secular = shifted_secular_scalar(lam, H, G, r, q, c2)
    return u, {
        "H": H,
        "G": G,
        "r": r,
        "q": q,
        "c2": c2,
        "x": x,
        "predecessor_residual_norm": float(np.linalg.norm(predecessor_residual)),
        "shell_residual": shell_residual,
        "secular_scalar": secular,
        "shell_residual_identity_error": abs(shell_residual - secular),
    }


def bracket_negative_secular_root(
    H: np.ndarray,
    G: np.ndarray,
    r: np.ndarray,
    q: float,
    c2: float,
    max_steps: int = 80,
) -> tuple[float, float]:
    """Bracket the retained negative root between lo<root<hi=0."""
    f0 = shifted_secular_scalar(0.0, H, G, r, q, c2)
    scale = max(abs(q), abs(f0), c2, 1.0)
    if not f0 < -1e-12 * scale:
        raise ValueError("zero-shift Schur scalar is not strictly negative")
    hi = 0.0
    lo = -1.0
    for _ in range(max_steps):
        flo = shifted_secular_scalar(lo, H, G, r, q, c2)
        if flo > 0.0:
            return lo, hi
        lo *= 2.0
    raise ArithmeticError("failed to bracket a negative secular root")


def find_negative_secular_root(
    H: np.ndarray,
    G: np.ndarray,
    r: np.ndarray,
    q: float,
    c2: float,
) -> tuple[float, tuple[float, float]]:
    lo, hi = bracket_negative_secular_root(H, G, r, q, c2)
    root = float(
        brentq(
            lambda z: shifted_secular_scalar(z, H, G, r, q, c2),
            lo,
            hi,
            xtol=1e-13,
            rtol=1e-13,
            maxiter=200,
        )
    )
    return root, (lo, hi)


def quadratic_normal(K: int) -> np.ndarray:
    """Raw coordinates of Lean's centeredQuadraticNormal."""
    d = np.arange(-K, K + 1, dtype=float)
    return d**2 - float(np.mean(d**2))


def centered_moment(u: np.ndarray, K: int, order: int) -> float:
    d = np.arange(-K, K + 1, dtype=float)
    v = np.asarray(u, dtype=float).reshape(-1)
    if len(v) != len(d):
        raise ValueError("vector length does not match centered grid")
    return float(np.dot(d**int(order), v))


def mixed_seventh_jet_from_m4(m4: float) -> float:
    """PR #163 exact normalization h^(7)(0)=-2(2*pi)^6 M4."""
    return float(-2.0 * (2.0 * math.pi) ** 6 * float(m4))


def explicit_source_moment_from_matrix(M: np.ndarray, u: np.ndarray, K: int) -> float:
    """Executable evenQuadraticSourceMoment = explicitCanonicalSourceMoment."""
    n2 = quadratic_normal(K)
    den = float(n2 @ n2)
    if not den > 0:
        raise ArithmeticError("quadratic-normal denominator vanished")
    return float((n2 @ M @ np.asarray(u, dtype=float).reshape(-1)) / den)


def source_moment_channel_record(L: float, K: int, u: np.ndarray) -> dict:
    """Decompose the quadratic-normal source moment through canonical channels."""
    n2 = quadratic_normal(K)
    den = float(n2 @ n2)
    v = np.asarray(u, dtype=float).reshape(-1)
    channels = signed_channel_matrices_L(L, K)
    values: dict[str, float] = {}
    for name, A in channels.items():
        values[name] = float((n2 @ A @ v) / den)

    arch = channels["arch_signed"]
    arch_diag = np.diag(np.diag(arch))
    arch_off = arch - arch_diag
    values["arch_signed_diagonal"] = float((n2 @ arch_diag @ v) / den)
    values["arch_signed_off_diagonal"] = float((n2 @ arch_off @ v) / den)

    total = float(sum(values[name] for name in ("pole", "arch_signed", "prime_signed", "scalar_shift")))
    direct = explicit_source_moment_from_matrix(canonical_source_matrix_L(L, K), v, K)
    return {
        "signed_channels": values,
        "sum": total,
        "direct": direct,
        "reconstruction_error": abs(total - direct),
        "arch_split_error": abs(
            values["arch_signed"]
            - values["arch_signed_diagonal"]
            - values["arch_signed_off_diagonal"]
        ),
    }


def opposite_parity_record(M: np.ndarray, K: int, selected_parity: Parity, tol: float = 2e-9) -> dict:
    parity: Parity = "odd" if selected_parity == "even" else "even"
    V = exact_parity_basis(K, parity)
    if V.cols == 0:
        return {
            "parity": parity,
            "dimension": 0,
            "min_form_eigenvalue": None,
            "classification": "GOOD_SIGNAL",
            "bad_witness_coeffs_in_exact_successor_basis": None,
        }
    Qv = orthonormal_columns(V)
    H = Qv.T @ M @ Qv
    H = (H + H.T) / 2.0
    vals, vecs = np.linalg.eigh(H)
    mineig = float(vals[0])
    if mineig < -tol:
        ambient = Qv @ vecs[:, 0]
        coeffs = np.linalg.lstsq(sympy_to_numpy(V), ambient, rcond=None)[0]
        witness = integer_direction_from_float(coeffs)
        classification = "BAD_SIGNAL"
    elif mineig > tol:
        witness = None
        classification = "GOOD_SIGNAL"
    else:
        witness = None
        classification = "NEAR_ZERO"
    return {
        "parity": parity,
        "dimension": V.cols,
        "min_form_eigenvalue": mineig,
        "classification": classification,
        "bad_witness_coeffs_in_exact_successor_basis": witness,
    }


def zero_shift_ray_agreement(M: np.ndarray, W_exact, c_exact) -> dict:
    """Cross-check integer-basis H^{-1}r against the legacy orthonormal formula."""
    W = sympy_to_numpy(W_exact)
    c = sympy_to_numpy(c_exact).reshape(-1)
    H, G, r, _q, _c2 = shifted_predecessor_system(M, W_exact, c_exact)
    if H.size:
        u_raw = c - W @ np.linalg.solve(H, r)
    else:
        u_raw = c.copy()

    c_unit = c / np.linalg.norm(c)
    if W_exact.cols:
        Qw = orthonormal_columns(W_exact)
        Ho = Qw.T @ M @ Qw
        ro = Qw.T @ M @ c_unit
        u_old = c_unit - Qw @ np.linalg.solve(Ho, ro)
    else:
        u_old = c_unit

    a = u_raw / np.linalg.norm(u_raw)
    b = u_old / np.linalg.norm(u_old)
    cosine = float(a @ b)
    return {
        "absolute_ray_cosine": abs(cosine),
        "ray_error": 1.0 - abs(cosine),
        "raw_gram_condition": float(np.linalg.cond(G)) if G.size else 1.0,
    }


def evaluate_shifted_state(
    Q: int,
    L: float,
    N: int,
    parity: Parity,
    tol: float = 2e-9,
) -> dict:
    """Evaluate one actual negative-root secular state in production normalization."""
    base = evaluate_selected_residual_state(Q, L, N, parity, tol=tol)
    K = N + 1
    M = canonical_source_matrix_L(L, K)
    W_exact = centered_predecessor_basis(N, parity)
    c_exact = exact_shell_generator(N, parity)
    H, G, r, q, c2 = shifted_predecessor_system(M, W_exact, c_exact)

    result = {
        "Q": int(Q),
        "L": float(L),
        "N": int(N),
        "Kstar": int(K),
        "parity": parity,
        "post150_scope": base["scope"],
        "selected_successor": base["successor"],
        "zero_shift_selected_residual": base["selected_residual"],
        "available": False,
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
    }

    if not base["scope"]["H1_predecessor_positive"]:
        result["failure"] = "selected_predecessor_not_positive"
        return result
    if not base["successor"]["bad_signal"]:
        result["failure"] = "selected_successor_not_bad"
        return result

    try:
        lam, bracket = find_negative_secular_root(H, G, r, q, c2)
    except (ValueError, ArithmeticError, np.linalg.LinAlgError) as exc:
        result["failure"] = f"negative_secular_root_not_reconstructed: {exc}"
        return result

    u, algebra = shifted_trial_vector(lam, M, W_exact, c_exact)
    u_norm = float(np.linalg.norm(u))
    if not u_norm > 0:
        result["failure"] = "shifted_trial_vanished"
        return result

    selected_eig = base["successor"]["min_form_eigenvalue"]
    eig_error = abs(float(selected_eig) - lam) if selected_eig is not None else math.inf
    m3 = centered_moment(u, K, 3)
    m4 = centered_moment(u, K, 4)
    h7 = mixed_seventh_jet_from_m4(m4) if parity == "even" else None
    opposite = opposite_parity_record(M, K, parity, tol=tol)
    zero_shift = zero_shift_ray_agreement(M, W_exact, c_exact)

    source = None
    if parity == "even":
        source = source_moment_channel_record(L, K, u)
        source["normalized_abs_source_moment"] = abs(source["direct"]) / u_norm
        source["normalized_abs_m4"] = abs(m4) / u_norm
        source["source_to_m4_ratio"] = (
            abs(source["direct"]) / abs(m4) if abs(m4) > 0 else math.inf
        )

    mp.mp.dps = 70
    s8_mp = canonical_riesz_endpoint_scalar_mp(8, Q, mp.mpf(str(L)))
    s8 = float(s8_mp)
    mixed_boundary_rhs = s8 * (abs(h7) ** 2) if h7 is not None else None

    result.update(
        {
            "available": True,
            "secular": {
                "lambda": lam,
                "bracket": [float(bracket[0]), float(bracket[1])],
                "f_zero": shifted_secular_scalar(0.0, H, G, r, q, c2),
                "selected_successor_min_eigenvalue": selected_eig,
                "root_eigenvalue_error": eig_error,
                "predecessor_residual_norm": algebra["predecessor_residual_norm"],
                "shell_residual": algebra["shell_residual"],
                "shell_residual_identity_error": algebra["shell_residual_identity_error"],
            },
            "zero_shift_crosscheck": zero_shift,
            "trial": {
                "norm": u_norm,
                "M3": m3,
                "M4": m4,
                "normalized_abs_M4": abs(m4) / u_norm,
                "mixed_seventh_jet": h7,
            },
            "explicit_source_moment": source,
            "opposite_parity": opposite,
            "endpoint_scalar": {
                "riesz_order": 8,
                "S8": s8,
                "sign": "POSITIVE" if s8 > 0 else ("NEGATIVE" if s8 < 0 else "ZERO"),
                "mixed_boundary_rhs": mixed_boundary_rhs,
            },
            "selected_bad_witness_coeffs_in_exact_successor_basis": base["successor"].get(
                "bad_witness_coeffs_in_exact_successor_basis"
            ),
            "nonclaims": [
                "Floating discovery is not theorem authority.",
                "The integer shell generator is only ray-equivalent to Lean's canonical cubic shell normalization.",
                "Odd-selected states do not inherit the even quadratic-normal source-jet theorem.",
                "No sourceMoment-to-M4 implication is asserted.",
                "No endpoint-scalar global sign theorem is asserted.",
                "RH remains OPEN.",
            ],
        }
    )
    return result
