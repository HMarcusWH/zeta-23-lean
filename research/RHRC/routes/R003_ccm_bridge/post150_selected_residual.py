#!/usr/bin/env python3
"""Exact finite geometry + fast post-#150 selected-residual diagnostics.

The geometry in this file is exact over Q:
- centered boundary-flat moments M0=M1=M2=0,
- exact reversal parity,
- centered one-step zero extension,
- the one-dimensional successor shell W^perp inside the successor parity space.

Floating point enters only when the production canonical source matrix is
inserted. Consequently this module is a discovery engine, not theorem
authority. Rigorous replay is implemented in
``certify_post150_selected_residual_scope.py``.
"""
from __future__ import annotations

import math
from functools import lru_cache
from math import gcd
from typing import Literal

import numpy as np
import sympy as sp

from canonical_source_numeric import (
    assert_in_fixed_cell,
    canonical_channel_energies_L,
    canonical_source_matrix_L,
)

Parity = Literal["even", "odd"]


def _primitive_integer_column(v: sp.Matrix) -> sp.Matrix:
    if v.cols != 1:
        raise ValueError("expected one column")
    if all(x == 0 for x in v):
        raise ValueError("zero vector cannot be primitive-normalized")
    den = 1
    for x in v:
        den = sp.ilcm(den, int(sp.denom(sp.together(x))))
    ints = [int(sp.Integer(sp.together(x) * den)) for x in v]
    g = 0
    for x in ints:
        g = gcd(g, abs(x))
    if g:
        ints = [x // g for x in ints]
    for x in ints:
        if x:
            if x < 0:
                ints = [-y for y in ints]
            break
    return sp.Matrix(ints)


def _constraint_matrix(N: int, parity: Parity) -> sp.Matrix:
    if N < 0:
        raise ValueError("require N>=0")
    if parity not in ("even", "odd"):
        raise ValueError("parity must be 'even' or 'odd'")
    idx = list(range(-N, N + 1))
    dim = len(idx)
    rows: list[list[int]] = []
    for k in range(3):
        rows.append([n**k for n in idx])
    sign = 1 if parity == "even" else -1
    for r in range((dim + 1) // 2):
        s = dim - 1 - r
        row = [0] * dim
        row[r] = 1
        row[s] -= sign
        rows.append(row)
    return sp.Matrix(rows)


@lru_cache(maxsize=None)
def exact_parity_basis(N: int, parity: Parity) -> sp.Matrix:
    """Integer-column basis of the exact Lean parity/boundary-flat carrier."""
    C = _constraint_matrix(N, parity)
    ns = C.nullspace()
    if ns:
        cols = [_primitive_integer_column(v) for v in ns]
        B = sp.Matrix.hstack(*cols)
    else:
        B = sp.zeros(2 * N + 1, 0)
    if C * B != sp.zeros(C.rows, B.cols):
        raise AssertionError("constructed basis violates exact constraints")
    expected = max(N - 1, 0)
    if B.cols != expected or B.rank() != expected:
        raise AssertionError(
            f"unexpected {parity} dimension at N={N}: got {B.cols}, expected {expected}"
        )
    return B


@lru_cache(maxsize=None)
def centered_predecessor_basis(N: int, parity: Parity) -> sp.Matrix:
    """Centered zero extension of V_N into the successor carrier V_(N+1)."""
    if N < 0:
        raise ValueError("require N>=0")
    B = exact_parity_basis(N, parity)
    out = sp.zeros(2 * (N + 1) + 1, B.cols)
    for r in range(B.rows):
        for c in range(B.cols):
            out[r + 1, c] = B[r, c]
    Csucc = _constraint_matrix(N + 1, parity)
    if Csucc * out != sp.zeros(Csucc.rows, out.cols):
        raise AssertionError("centered predecessor escaped successor parity carrier")
    return out


@lru_cache(maxsize=None)
def exact_shell_generator(N: int, parity: Parity) -> sp.Matrix:
    """Exact integer generator of W^perp ∩ V_(N+1).

    The formal project uses the nonzero cubic shell vector as a canonical
    normalization. This generator need not have that normalization. Since the
    shell is one-dimensional, selected-residual sign is invariant under
    replacing the canonical shell vector by any nonzero scalar multiple.
    """
    if N < 1:
        raise ValueError("shell diagnostics require predecessor N>=1")
    V = exact_parity_basis(N + 1, parity)
    W = centered_predecessor_basis(N, parity)
    equations = W.T * V
    ns = equations.nullspace()
    if len(ns) != 1:
        raise AssertionError(f"expected one-dimensional intrinsic shell, got nullity {len(ns)}")
    c = _primitive_integer_column(V * ns[0])
    if W.T * c != sp.zeros(W.cols, 1):
        raise AssertionError("shell generator is not orthogonal to predecessor")
    if c == sp.zeros(c.rows, 1):
        raise AssertionError("zero shell generator")
    return c


def sympy_to_numpy(A: sp.Matrix) -> np.ndarray:
    return np.array([[float(A[r, c]) for c in range(A.cols)] for r in range(A.rows)])


def integer_direction_from_float(v: np.ndarray, scale: int = 10**8) -> list[int]:
    """Deterministically rationalize a discovery eigenvector for Arb replay."""
    a = np.asarray(v, dtype=float).reshape(-1)
    if not len(a) or not np.max(np.abs(a)) > 0:
        raise ValueError("cannot rationalize zero direction")
    a = a / np.max(np.abs(a))
    ints = [int(round(scale * x)) for x in a]
    if not any(ints):
        ints[int(np.argmax(np.abs(a)))] = 1
    g = 0
    for x in ints:
        g = gcd(g, abs(x))
    if g:
        ints = [x // g for x in ints]
    for x in ints:
        if x:
            if x < 0:
                ints = [-y for y in ints]
            break
    return ints


def orthonormal_columns(B: sp.Matrix) -> np.ndarray:
    """Numerically orthonormalize an exact full-column-rank basis."""
    if B.cols == 0:
        return np.zeros((B.rows, 0), dtype=float)
    X = sympy_to_numpy(B)
    Q, R = np.linalg.qr(X, mode="reduced")
    if np.min(np.abs(np.diag(R))) < 1e-14:
        raise ArithmeticError("exact basis became numerically rank-deficient")
    return Q


def _restricted_form(M: np.ndarray, B: sp.Matrix) -> np.ndarray:
    if B.cols == 0:
        return np.zeros((0, 0), dtype=float)
    Q = orthonormal_columns(B)
    return Q.T @ M @ Q


def _raw_restricted_form(M: np.ndarray, B: sp.Matrix) -> np.ndarray:
    if B.cols == 0:
        return np.zeros((0, 0), dtype=float)
    X = sympy_to_numpy(B)
    return X.T @ M @ X


def _min_eig(H: np.ndarray) -> float:
    if H.size == 0:
        return math.inf
    return float(np.linalg.eigvalsh((H + H.T) / 2.0)[0])


def _min_abs_eig(H: np.ndarray) -> float:
    if H.size == 0:
        return math.inf
    vals = np.linalg.eigvalsh((H + H.T) / 2.0)
    return float(np.min(np.abs(vals)))


def same_aperture_smaller_size_goodness(
    L: float,
    predecessor_N: int,
    Q: int,
    tol: float = 2e-9,
) -> dict:
    """Discovery version of 'all M<K*=N+1 are good in both parities'."""
    rows = []
    all_good = True
    for M in range(predecessor_N + 1):
        source = canonical_source_matrix_L(L, M)
        for parity in ("even", "odd"):
            V = exact_parity_basis(M, parity)
            H = _restricted_form(source, V)
            mineig = _min_eig(H)
            good = mineig >= -tol
            rows.append(
                {
                    "size": M,
                    "parity": parity,
                    "dimension": V.cols,
                    "min_form_eigenvalue": mineig if math.isfinite(mineig) else None,
                    "good_with_tolerance": good,
                }
            )
            all_good = all_good and good
    return {"all_good": all_good, "rows": rows, "tolerance": tol}


def evaluate_selected_residual_state(
    Q: int,
    L: float,
    N: int,
    parity: Parity,
    tol: float = 2e-9,
) -> dict:
    """Evaluate one post-#150 predecessor/successor state in production normalization."""
    if N < 1:
        raise ValueError("require predecessor N>=1")
    assert_in_fixed_cell(Q, L)

    K = N + 1
    Vprev = exact_parity_basis(N, parity)
    W = centered_predecessor_basis(N, parity)
    Vsucc = exact_parity_basis(K, parity)
    c_exact = exact_shell_generator(N, parity)

    Mprev = canonical_source_matrix_L(L, N)
    Msucc = canonical_source_matrix_L(L, K)

    Hprev_raw = _raw_restricted_form(Mprev, Vprev)
    H_raw = _raw_restricted_form(Msucc, W)
    flow_error = float(np.max(np.abs(H_raw - Hprev_raw))) if H_raw.size or Hprev_raw.size else 0.0

    Qw = orthonormal_columns(W)
    Qs = orthonormal_columns(Vsucc)
    H = Qw.T @ Msucc @ Qw if W.cols else np.zeros((0, 0))
    Hsucc = Qs.T @ Msucc @ Qs if Vsucc.cols else np.zeros((0, 0))

    cn = sympy_to_numpy(c_exact).reshape(-1)
    cn = cn / np.linalg.norm(cn)

    if W.cols:
        r = Qw.T @ Msucc @ cn
        min_abs = _min_abs_eig(H)
        scale = max(float(np.linalg.norm(H, 2)), 1.0)
        regular = min_abs > tol * scale
        if regular:
            x = np.linalg.solve(H, r)
        else:
            x = np.linalg.lstsq(H, r, rcond=None)[0]
        predecessor_part = Qw @ x
    else:
        r = np.zeros(0)
        x = np.zeros(0)
        predecessor_part = np.zeros_like(cn)
        min_abs = math.inf
        regular = True

    q_shell = float(cn @ Msucc @ cn)
    schur = float(q_shell - (r @ x if len(r) else 0.0))
    u = cn - predecessor_part
    direct = float(u @ Msucc @ u)
    schur_identity_error = abs(direct - schur)

    prev_min = _min_eig(H)
    pred_scale = max(float(np.linalg.norm(H, 2)), 1.0) if H.size else 1.0
    predecessor_positive = prev_min > tol * pred_scale
    succ_vals, succ_vecs = (
        np.linalg.eigh((Hsucc + Hsucc.T) / 2.0)
        if Hsucc.size
        else (np.array([]), np.zeros((0, 0)))
    )
    succ_min = float(succ_vals[0]) if len(succ_vals) else math.inf
    successor_bad = succ_min < -tol
    if successor_bad:
        ambient_bad = Qs @ succ_vecs[:, 0]
        exact_coords = np.linalg.lstsq(sympy_to_numpy(Vsucc), ambient_bad, rcond=None)[0]
        bad_witness_coeffs = integer_direction_from_float(exact_coords)
    else:
        bad_witness_coeffs = None

    smaller = same_aperture_smaller_size_goodness(L, N, Q, tol=tol)

    H0 = regular
    H1 = H0 and predecessor_positive
    H2 = H1 and successor_bad
    H3 = H2 and smaller["all_good"]
    negative = direct < -tol

    highest = "NONE"
    for name, flag in (("H0", H0), ("H1", H1), ("H2", H2), ("H3", H3)):
        if flag:
            highest = name

    channels = canonical_channel_energies_L(L, K, u)

    return {
        "Q": Q,
        "L": L,
        "N": N,
        "Kstar": K,
        "parity": parity,
        "dimensions": {
            "predecessor_parity": Vprev.cols,
            "successor_parity": Vsucc.cols,
            "predecessor_image": W.cols,
        },
        "geometry": {
            "shell_generator": [int(x) for x in c_exact],
            "shell_normalization": (
                "exact integer generator of the formal one-dimensional intrinsic shell; "
                "sign-equivalent to the canonical cubic shell normalization"
            ),
        },
        "flow": {"restricted_form_max_error": flow_error},
        "predecessor": {
            "min_form_eigenvalue": prev_min if math.isfinite(prev_min) else None,
            "min_abs_form_eigenvalue": min_abs if math.isfinite(min_abs) else None,
            "regular": regular,
            "positive_definite_signal": predecessor_positive,
        },
        "successor": {
            "min_form_eigenvalue": succ_min if math.isfinite(succ_min) else None,
            "bad_signal": successor_bad,
            "bad_witness_coeffs_in_exact_successor_basis": bad_witness_coeffs,
        },
        "selected_residual": {
            "shell_energy": q_shell,
            "schur_energy": schur,
            "direct_trial_energy": direct,
            "identity_error": schur_identity_error,
            "negative_signal": negative,
            "channel_energies": channels,
        },
        "same_aperture_ancestry": smaller,
        "scope": {
            "H0_regular": H0,
            "H1_predecessor_positive": H1,
            "H2_selected_successor_bad": H2,
            "H3_all_smaller_sizes_both_parities_good_same_aperture": H3,
            "highest": highest,
        },
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
    }


def exact_geometry_self_check(max_N: int = 8) -> dict:
    checked = []
    for N in range(1, max_N + 1):
        for parity in ("even", "odd"):
            V = exact_parity_basis(N, parity)
            if V.cols != N - 1:
                raise AssertionError("parity dimension regression")
            Vs = exact_parity_basis(N + 1, parity)
            W = centered_predecessor_basis(N, parity)
            c = exact_shell_generator(N, parity)
            if Vs.cols != N or W.cols != N - 1:
                raise AssertionError("one-step dimension regression")
            if W.T * c != sp.zeros(W.cols, 1):
                raise AssertionError("shell orthogonality regression")
            checked.append(
                {
                    "N": N,
                    "parity": parity,
                    "dim_VN": V.cols,
                    "dim_successor": Vs.cols,
                    "dim_W": W.cols,
                }
            )
    return {"status": "PASS", "checked": checked}
