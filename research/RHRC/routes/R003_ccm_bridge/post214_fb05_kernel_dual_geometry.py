#!/usr/bin/env python3
"""Post-#214 exact Pair-D kernel dual-geometry audit.

Research/falsification tooling only.

The #213 Lean theorem identifies the complete Pair-D source functional with the
same finite-matrix quadratic-normal moment already implemented by the canonical
source evaluators.  For the active K=3 even boundary-flat carrier this module
therefore studies two covectors on an exact two-dimensional space:

    F_L(v) = explicitCanonicalSourceMoment(L,3,v)
    G(v)   = M4(v)

The #163 theorem gives h_v^(7)(0) = -2*(2*pi)^6*M4(v), so sign geometry for
Re(conj(F_L(v))*M4(v)) translates exactly to the seventh-jet pairing up to one
known negative scalar.

No result in this module is Lean theorem authority.  RH remains OPEN.
"""
from __future__ import annotations

import math
from typing import Iterable

import numpy as np
import sympy as sp
from flint import arb, arb_mat

from canonical_source_arb import (
    ball_record,
    canonical_source_matrix,
    definitely_negative,
    fixed_cell_membership,
    signed_channel_matrices,
)
from canonical_source_numeric import canonical_source_matrix_L
from post150_selected_residual import exact_parity_basis, sympy_to_numpy
from post166_fb05_cell_interval import cell_coordinate_L

TARGET_K = 3
TARGET_PARITY = "even"


def even_boundary_flat_basis_exact(K: int = TARGET_K) -> sp.Matrix:
    if K != TARGET_K:
        raise ValueError("post-#214 audit is frozen at K=3")
    B = exact_parity_basis(K, TARGET_PARITY)
    if B.cols != 2:
        raise AssertionError(f"expected 2D even boundary-flat carrier, got {B.cols}")
    return B


def centered_indices(K: int) -> list[int]:
    return list(range(-K, K + 1))


def quadratic_normal_exact(K: int = TARGET_K) -> sp.Matrix:
    idx = centered_indices(K)
    mean_sq = sp.Rational(sum(d * d for d in idx), len(idx))
    return sp.Matrix([sp.Integer(d * d) - mean_sq for d in idx])


def moment_four_covector_exact(B: sp.Matrix, K: int = TARGET_K) -> sp.Matrix:
    row = sp.Matrix([[sp.Integer(d) ** 4 for d in centered_indices(K)]])
    return sp.simplify(row * B)


def displacement_gram_exact(B: sp.Matrix, K: int = TARGET_K) -> sp.Matrix:
    D2 = sp.diag(*[sp.Integer(d) ** 2 for d in centered_indices(K)])
    return sp.simplify(B.T * D2 * B)


def quadratic_normal_denominator_exact(K: int = TARGET_K) -> sp.Expr:
    n2 = quadratic_normal_exact(K)
    return sp.simplify((n2.T * n2)[0])


def _arb_matrix_from_sympy(A: sp.Matrix) -> arb_mat:
    return arb_mat([
        [arb(str(A[r, c])) for c in range(A.cols)]
        for r in range(A.rows)
    ])


def _matrix_overlap(A: arb_mat, B: arb_mat) -> bool:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        return False
    return all(
        bool((A[r, c] - B[r, c]).contains(0))
        for r in range(A.nrows())
        for c in range(A.ncols())
    )


def _covector_overlap(a: list[arb], b: list[arb]) -> bool:
    return len(a) == len(b) and all(bool((x - y).contains(0)) for x, y in zip(a, b))


def kernel_covector_from_matrix_arb(
    M: arb_mat,
    B: sp.Matrix,
    K: int = TARGET_K,
) -> list[arb]:
    n2 = quadratic_normal_exact(K)
    den = quadratic_normal_denominator_exact(K)
    if den == 0:
        raise ArithmeticError("quadratic-normal denominator vanished")
    N = _arb_matrix_from_sympy(n2.T)
    Bb = _arb_matrix_from_sympy(B)
    raw = N * M * Bb
    denb = arb(str(den))
    return [raw[0, j] / denb for j in range(B.cols)]


def kernel_covector_arb(L: arb, Q: int, K: int = TARGET_K) -> dict:
    B = even_boundary_flat_basis_exact(K)
    membership = fixed_cell_membership(Q, L)
    if not membership["certified"]:
        raise ValueError("center aperture is not certified inside requested fixed cell")

    direct = canonical_source_matrix(L, K, Q)
    channels = signed_channel_matrices(L, K, Q)
    rebuilt = (
        channels["pole"]
        + channels["arch_signed"]
        + channels["prime_signed"]
        + channels["scalar_shift"]
    )
    if not _matrix_overlap(direct, rebuilt):
        raise AssertionError("direct canonical matrix and channel reconstruction are disjoint")

    f_direct = kernel_covector_from_matrix_arb(direct, B, K)
    f_rebuilt = kernel_covector_from_matrix_arb(rebuilt, B, K)
    if not _covector_overlap(f_direct, f_rebuilt):
        raise AssertionError("direct and reconstructed kernel covectors are disjoint")

    return {
        "basis": B,
        "direct_matrix": direct,
        "rebuilt_matrix": rebuilt,
        "f_direct": f_direct,
        "f_rebuilt": f_rebuilt,
        "matrix_reconstruction_overlap": True,
        "covector_reconstruction_overlap": True,
        "fixed_cell_membership": membership,
    }


def moment_four_covector_arb(B: sp.Matrix, K: int = TARGET_K) -> list[arb]:
    g = moment_four_covector_exact(B, K)
    return [arb(str(g[0, j])) for j in range(g.cols)]


def dual_wedge(f: list[arb], g: list[arb]) -> arb:
    if len(f) != 2 or len(g) != 2:
        raise ValueError("wedge classifier is frozen to two covectors in dimension 2")
    return f[0] * g[1] - f[1] * g[0]


def product_form_arb(f: list[arb], g: list[arb]) -> list[list[arb]]:
    if len(f) != 2 or len(g) != 2:
        raise ValueError("product form is frozen to dimension 2")
    return [
        [f[0] * g[0], (f[0] * g[1] + g[0] * f[1]) / 2],
        [(f[0] * g[1] + g[0] * f[1]) / 2, f[1] * g[1]],
    ]


def det2_arb(H: list[list[arb]]) -> arb:
    return H[0][0] * H[1][1] - H[0][1] * H[1][0]


def generalized_extrema_2x2(
    H: list[list[arb]],
    G: sp.Matrix,
) -> tuple[arb | None, arb | None, arb]:
    if G.shape != (2, 2):
        raise ValueError("energy Gram must be 2x2")
    g00 = arb(str(G[0, 0]))
    g01 = arb(str(G[0, 1]))
    g11 = arb(str(G[1, 1]))
    a = g00 * g11 - g01 * g01
    if not bool(a > 0):
        raise AssertionError("D-energy Gram is not positive definite")

    b = -(H[0][0] * g11 + H[1][1] * g00 - 2 * H[0][1] * g01)
    c = det2_arb(H)
    disc = b * b - 4 * a * c
    if not bool(disc > 0):
        return None, None, disc
    s = disc.sqrt()
    r1 = (-b - s) / (2 * a)
    r2 = (-b + s) / (2 * a)
    return r1, r2, disc


def covector_correlation_arb(f: list[arb], g: list[arb]) -> arb | None:
    ff = sum((x * x for x in f), arb(0))
    gg = sum((x * x for x in g), arb(0))
    if not bool(ff > 0) or not bool(gg > 0):
        return None
    fg = sum((x * y for x, y in zip(f, g)), arb(0))
    return abs(fg) / (ff * gg).sqrt()


def scalar_identity_annihilation_exact(B: sp.Matrix, K: int = TARGET_K) -> sp.Matrix:
    n2 = quadratic_normal_exact(K)
    return sp.simplify(n2.T * B)


def geometry_record_arb(L: arb, Q: int, K: int = TARGET_K) -> dict:
    cov = kernel_covector_arb(L, Q, K)
    B = cov["basis"]
    f = cov["f_direct"]
    g = moment_four_covector_arb(B, K)
    wedge = dual_wedge(f, g)
    H = product_form_arb(f, g)
    detH = det2_arb(H)
    identity_residual = detH + wedge * wedge / 4
    identity_overlap = bool(identity_residual.contains(0))
    G = displacement_gram_exact(B, K)
    rmin, rmax, disc = generalized_extrema_2x2(H, G)
    corr = covector_correlation_arb(f, g)

    independent = not bool(wedge.contains(0))
    sign_indefinite = bool(definitely_negative(detH))
    if independent:
        classification = "FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED"
    elif all(bool(x.contains(0)) for x in [wedge]):
        classification = "DUAL_PROPORTIONALITY_NOT_FALSIFIED"
    else:
        classification = "DUAL_GEOMETRY_UNRESOLVED"

    return {
        "classification": classification,
        "full_space_sign_indefinite_certified": sign_indefinite,
        "kernel_covector": [ball_record(x) for x in f],
        "kernel_covector_rebuilt": [ball_record(x) for x in cov["f_rebuilt"]],
        "moment_four_covector_exact": [str(moment_four_covector_exact(B, K)[0, j]) for j in range(B.cols)],
        "wedge": ball_record(wedge),
        "wedge_excludes_zero": independent,
        "product_form": [[ball_record(x) for x in row] for row in H],
        "product_form_det": ball_record(detH),
        "det_equals_neg_wedge_sq_over_four_overlap": identity_overlap,
        "det_identity_residual": ball_record(identity_residual),
        "D_energy_gram_exact": [[str(G[r, c]) for c in range(G.cols)] for r in range(G.rows)],
        "generalized_discriminant": ball_record(disc),
        "generalized_R_min": None if rmin is None else ball_record(rmin),
        "generalized_R_max": None if rmax is None else ball_record(rmax),
        "covector_abs_correlation": None if corr is None else ball_record(corr),
        "matrix_reconstruction_overlap": cov["matrix_reconstruction_overlap"],
        "covector_reconstruction_overlap": cov["covector_reconstruction_overlap"],
        "fixed_cell_membership": cov["fixed_cell_membership"],
        "scalar_identity_annihilation_exact": [
            str(scalar_identity_annihilation_exact(B, K)[0, j]) for j in range(B.cols)
        ],
    }


def geometry_record_float(Q: int, t: float, K: int = TARGET_K) -> dict:
    B = even_boundary_flat_basis_exact(K)
    X = sympy_to_numpy(B)
    L = cell_coordinate_L(Q, t)
    M = canonical_source_matrix_L(L, K)
    n2 = np.array([float(x) for x in quadratic_normal_exact(K)], dtype=float)
    den = float(n2 @ n2)
    f = (n2 @ M @ X) / den
    g = np.array([float(moment_four_covector_exact(B, K)[0, j]) for j in range(B.cols)])
    wedge = float(f[0] * g[1] - f[1] * g[0])
    H = 0.5 * (np.outer(f, g) + np.outer(g, f))
    G = np.array(displacement_gram_exact(B, K), dtype=float)
    vals = np.linalg.eigvals(np.linalg.solve(G, H))
    vals = np.sort(np.real_if_close(vals).astype(float))
    corr = abs(float(f @ g)) / math.sqrt(float(f @ f) * float(g @ g))
    return {
        "Q": int(Q),
        "t": float(t),
        "L": float(L),
        "kernel_covector": [float(x) for x in f],
        "moment_four_covector": [float(x) for x in g],
        "wedge": wedge,
        "product_form_det": float(np.linalg.det(H)),
        "generalized_R_min": float(vals[0]),
        "generalized_R_max": float(vals[-1]),
        "covector_abs_correlation": float(corr),
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
    }


def exact_geometry_invariants(K: int = TARGET_K) -> dict:
    B = even_boundary_flat_basis_exact(K)
    n2 = quadratic_normal_exact(K)
    g = moment_four_covector_exact(B, K)
    G = displacement_gram_exact(B, K)
    return {
        "basis": [[str(B[r, c]) for c in range(B.cols)] for r in range(B.rows)],
        "dimension": int(B.cols),
        "quadratic_normal": [str(x) for x in n2],
        "quadratic_normal_denominator": str(quadratic_normal_denominator_exact(K)),
        "moment_four_covector": [str(g[0, j]) for j in range(g.cols)],
        "D_energy_gram": [[str(G[r, c]) for c in range(G.cols)] for r in range(G.rows)],
        "D_energy_gram_det": str(sp.simplify(G.det())),
        "scalar_identity_annihilation": [
            str(scalar_identity_annihilation_exact(B, K)[0, j]) for j in range(B.cols)
        ],
    }
