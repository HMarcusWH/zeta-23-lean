#!/usr/bin/env python3
"""Prime-cutoff threshold jet utilities for the post-#167 FB-05 audit.

The natural threshold coordinate is the already-formalized source coordinate

    omega_q(L) = 1 - log(q) / L.

At L = log(q), omega = 0 and the entering prime-power source atom vanishes.
The canonical source subtracts the von-Mangoldt weighted source matrix.

The exact symbolic layer works on the real coefficient matrices of the source
atom Taylor series.  After restriction to the exact boundary-flat parity
carrier, it tests the first surviving moment channels without fitting any
numerical data.

Floating and Arb helpers below are research/audit tooling only.  No result from
this module is Lean theorem authority.  RH remains OPEN.
"""
from __future__ import annotations

import math

import numpy as np
import sympy as sp
from flint import arb, arb_mat

from canonical_source_arb import ball_record, von_mangoldt
from canonical_source_numeric import canonical_source_matrix_L
from post150_selected_residual import exact_parity_basis, orthonormal_columns, sympy_to_numpy
from post166_fb05_cell_interval import _arb_matrix_from_sympy, principal_determinants_arb


def source_coordinate(q: int, L: float) -> float:
    if q < 2 or not L > 0:
        raise ValueError("require q>=2 and L>0")
    return 1.0 - math.log(float(q)) / float(L)


def aperture_from_source_coordinate(q: int, omega: float) -> float:
    if q < 2 or not omega < 1.0:
        raise ValueError("require q>=2 and omega<1")
    return math.log(float(q)) / (1.0 - float(omega))


def source_entry_float(omega: float, n: int, m: int) -> float:
    if n == m:
        return 2.0 * omega * math.cos(2.0 * math.pi * n * omega)
    return (
        math.sin(2.0 * math.pi * n * omega)
        - math.sin(2.0 * math.pi * m * omega)
    ) / (math.pi * (n - m))


def source_matrix_float(omega: float, K: int) -> np.ndarray:
    if K < 0:
        raise ValueError("require K>=0")
    idx = list(range(-K, K + 1))
    M = np.empty((len(idx), len(idx)), dtype=float)
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            value = source_entry_float(omega, n, idx[c])
            M[r, c] = value
            M[c, r] = value
    return M


def source_entry_arb(omega: arb, n: int, m: int) -> arb:
    pi = arb.pi()
    if n == m:
        return 2 * omega * (2 * pi * n * omega).cos()
    return ((2 * pi * n * omega).sin() - (2 * pi * m * omega).sin()) / (pi * (n - m))


def source_matrix_arb(omega: arb, K: int) -> arb_mat:
    if K < 0:
        raise ValueError("require K>=0")
    idx = list(range(-K, K + 1))
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            value = source_entry_arb(omega, n, idx[c])
            rows[r][c] = value
            rows[c][r] = value
    return arb_mat(rows)


def von_mangoldt_weight_float(q: int) -> float:
    return float(von_mangoldt(q)) / math.sqrt(float(q))


def von_mangoldt_weight_arb(q: int) -> arb:
    return von_mangoldt(q) / arb(q).sqrt()


def canonical_entering_atom_float(q: int, K: int, omega: float) -> np.ndarray:
    """Signed canonical increment: -(Lambda(q)/sqrt(q))*sourceMatrix(omega)."""
    return -von_mangoldt_weight_float(q) * source_matrix_float(omega, K)


def canonical_entering_atom_arb(q: int, K: int, omega: arb) -> arb_mat:
    return -von_mangoldt_weight_arb(q) * source_matrix_arb(omega, K)


def centered_moment_row(K: int, B: sp.Matrix, order: int) -> sp.Matrix:
    if B.rows != 2 * K + 1 or order < 0:
        raise ValueError("basis shape/order mismatch")
    idx = list(range(-K, K + 1))
    return sp.Matrix([[sum(sp.Integer(idx[r]) ** order * B[r, c] for r in range(B.rows)) for c in range(B.cols)]])


def normalized_source_series_coefficient_sympy(K: int, k: int) -> sp.Matrix:
    """Coefficient of omega^(2k+1), divided by (2*pi)^(2k).

    The exact divided-difference coefficient is

      2*(-1)^k/(2k+1)! * sum_{j=0}^{2k} n^(2k-j)m^j.

    Keeping the common pi power factored out makes the acceptance identities
    exact over Q and cheap enough for CI.
    """
    if K < 0 or k < 0:
        raise ValueError("require K,k>=0")
    idx = list(range(-K, K + 1))
    scale = sp.Rational(2 * ((-1) ** k), math.factorial(2 * k + 1))
    return sp.Matrix(
        len(idx),
        len(idx),
        lambda r, c: sp.simplify(
            scale * sum(sp.Integer(idx[r]) ** (2 * k - j) * sp.Integer(idx[c]) ** j for j in range(2 * k + 1))
        ),
    )


def restricted_normalized_series_coefficient_sympy(K: int, parity: str, k: int) -> sp.Matrix:
    B = exact_parity_basis(K, parity)
    C = normalized_source_series_coefficient_sympy(K, k)
    return sp.simplify(B.T * C * B)


def predicted_odd_order7_normalized(K: int) -> sp.Matrix:
    B = exact_parity_basis(K, "odd")
    m3 = centered_moment_row(K, B, 3)
    return sp.Rational(-2, math.factorial(7)) * (m3.T * m3)


def predicted_even_order9_normalized(K: int) -> sp.Matrix:
    B = exact_parity_basis(K, "even")
    m4 = centered_moment_row(K, B, 4)
    return sp.Rational(2, math.factorial(9)) * (m4.T * m4)


def predicted_canonical_leading_matrix_float(q: int, K: int, parity: str) -> np.ndarray:
    """Leading signed canonical prime-entry coefficient in source coordinate."""
    B = exact_parity_basis(K, parity)
    weight = von_mangoldt_weight_float(q)
    if parity == "odd":
        m = np.asarray(centered_moment_row(K, B, 3), dtype=float)
        return weight * 2.0 * (2.0 * math.pi) ** 6 / math.factorial(7) * (m.T @ m)
    if parity == "even":
        m = np.asarray(centered_moment_row(K, B, 4), dtype=float)
        return -weight * 2.0 * (2.0 * math.pi) ** 8 / math.factorial(9) * (m.T @ m)
    raise ValueError("parity must be even or odd")


def restricted_canonical_entering_atom_float(q: int, K: int, parity: str, omega: float) -> np.ndarray:
    B = exact_parity_basis(K, parity)
    X = sympy_to_numpy(B)
    return X.T @ canonical_entering_atom_float(q, K, omega) @ X


def restricted_canonical_entering_atom_arb(q: int, K: int, parity: str, omega: arb) -> arb_mat:
    B = exact_parity_basis(K, parity)
    Bb = _arb_matrix_from_sympy(B)
    return Bb.transpose() * canonical_entering_atom_arb(q, K, omega) * Bb


def _raw_restriction_float(M: np.ndarray, B: sp.Matrix) -> np.ndarray:
    X = sympy_to_numpy(B)
    return X.T @ M @ X if B.cols else np.zeros((0, 0), dtype=float)


def successor_barrier_at_L_float(L: float, predecessor_N: int, parity: str) -> dict:
    K = predecessor_N + 1
    B = exact_parity_basis(K, parity)
    M = canonical_source_matrix_L(float(L), K)
    Hraw = _raw_restriction_float(M, B)
    Qb = orthonormal_columns(B)
    H = Qb.T @ M @ Qb if B.cols else np.zeros((0, 0), dtype=float)
    Hs = (H + H.T) / 2.0 if H.size else H
    eigs = np.linalg.eigvalsh(Hs) if H.size else np.array([], dtype=float)
    mineig = float(eigs[0]) if len(eigs) else math.inf
    maxeig = float(eigs[-1]) if len(eigs) else math.inf
    scale = max(float(np.linalg.norm(Hs, 2)), 1e-300) if H.size else 1.0
    minors = [float(np.linalg.det(Hraw[:j, :j])) for j in range(1, Hraw.shape[0] + 1)]
    pivot = final_sylvester_pivot_float(Hraw)
    return {
        "L": float(L),
        "N": predecessor_N,
        "Kstar": K,
        "parity": parity,
        "dimension": int(B.cols),
        "min_eigenvalue": mineig if math.isfinite(mineig) else None,
        "max_eigenvalue": maxeig if math.isfinite(maxeig) else None,
        "normalized_min_eigenvalue": mineig / scale if math.isfinite(mineig) else None,
        "raw_leading_principal_determinants": minors,
        "final_sylvester_pivot": pivot,
        "normalized_determinant": float(np.linalg.det(Hs)) / (scale ** H.shape[0]) if H.size else 1.0,
    }


def final_sylvester_pivot_float(H: np.ndarray) -> float | None:
    if H.shape[0] == 0:
        return None
    detn = float(np.linalg.det(H))
    if H.shape[0] == 1:
        return detn
    detprev = float(np.linalg.det(H[:-1, :-1]))
    if detprev == 0.0:
        return None
    return detn / detprev


def final_sylvester_pivot_arb(H: arb_mat) -> arb | None:
    minors = principal_determinants_arb(H)
    if not minors:
        return None
    if len(minors) == 1:
        return minors[0]
    if minors[-2].contains(0):
        return None
    return minors[-1] / minors[-2]


def arb_matrix_record(H: arb_mat) -> list[list[dict]]:
    return [[ball_record(H[r, c]) for c in range(H.ncols())] for r in range(H.nrows())]
