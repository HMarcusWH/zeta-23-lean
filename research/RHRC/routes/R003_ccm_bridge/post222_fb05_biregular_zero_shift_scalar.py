#!/usr/bin/env python3
"""Exact-geometry / Arb evaluator for the post-#222 bi-regular zero-shift scalar.

The formal post-#222 normal form reduces the retained bi-regular branch to the
real sign of the odd zero-shift response

    sigma_- = alpha_0 * sigma_+ + Gamma_0 * mu_0.

This module reconstructs the exact finite geometry used by Lean and evaluates
that identity with Arb enclosures.  Static geometry is exact SymPy rational
algebra; Arb is introduced only for the canonical source matrix and the
resulting linear solves.

Claim firewall:
* finite research audit only, not Lean theorem authority;
* no adaptive target search, sign fitting, or theorem promotion;
* no FB-05 closure, negative-root exclusion, finite-to-infinite closure, or RH claim.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import sympy as sp
from flint import arb, arb_mat

from canonical_source_arb import (
    ball_record,
    definitely_negative,
    definitely_positive,
    to_arb_rational,
)
from post150_selected_residual import (
    centered_predecessor_basis,
    exact_parity_basis,
    exact_shell_generator,
)
from post166_fb05_cell_interval import (
    _arb_matrix_from_sympy,
    cell_coordinate_L_arb,
    fixed_q_canonical_source_matrix_arb,
    principal_determinants_arb,
)


def _q(x: sp.Expr) -> sp.Rational:
    return sp.Rational(x)


def _arb_of_sympy(x: sp.Expr) -> arb:
    q = _q(x)
    return to_arb_rational(int(q.p), int(q.q))


def arb_matrix_from_sympy_rational(A: sp.Matrix) -> arb_mat:
    if A.cols == 0:
        return arb_mat(A.rows, 0)
    return arb_mat([[_arb_of_sympy(A[r, c]) for c in range(A.cols)] for r in range(A.rows)])


def _centered_indices(K: int) -> list[int]:
    return list(range(-K, K + 1))


def _power_vector(K: int, power: int) -> sp.Matrix:
    return sp.Matrix([sp.Integer(n) ** power for n in _centered_indices(K)])


def _orthogonal_projection_exact(B: sp.Matrix, v: sp.Matrix) -> sp.Matrix:
    """Euclidean orthogonal projection onto col(B), in exact rational algebra."""
    if B.cols == 0:
        return sp.zeros(B.rows, 1)
    gram = B.T * B
    if gram.det() == 0:
        raise AssertionError("projection basis has singular Gram matrix")
    out = B * gram.inv() * B.T * v
    if B.T * (v - out) != sp.zeros(B.cols, 1):
        raise AssertionError("exact orthogonal projection check failed")
    return sp.simplify(out)


def odd_cubic_compression_vector_exact(K: int) -> sp.Matrix:
    """Lean's oddCubicCompressionVector K = P_odd(d^3)."""
    if K < 2:
        raise ValueError("odd cubic compression requires K>=2")
    Vodd = exact_parity_basis(K, "odd")
    g = _orthogonal_projection_exact(Vodd, _power_vector(K, 3))
    if g == sp.zeros(2 * K + 1, 1):
        raise AssertionError("odd cubic compression unexpectedly vanished")
    return g


def successor_pulled_back_cubic_exact(N: int) -> sp.Matrix:
    """Lean's successorPulledBackCubicCompressionVector N.

    Solve D g_plus = g_minus exactly inside the even boundary-flat carrier.
    """
    if N < 1:
        raise ValueError("require N>=1")
    K = N + 1
    g_minus = odd_cubic_compression_vector_exact(K)
    Veven = exact_parity_basis(K, "even")
    D = sp.diag(*_centered_indices(K))
    DB = D * Veven
    sol, params = DB.gauss_jordan_solve(g_minus)
    if params.rows != 0:
        raise AssertionError("D pullback was not uniquely determined")
    g_plus = sp.simplify(Veven * sol)
    if D * g_plus != g_minus:
        raise AssertionError("exact D pullback identity failed")
    return g_plus


def successor_parity_cubic_vector_exact(N: int, parity: str) -> sp.Matrix:
    if parity == "odd":
        return odd_cubic_compression_vector_exact(N + 1)
    if parity == "even":
        return successor_pulled_back_cubic_exact(N)
    raise ValueError("parity must be even or odd")


def canonical_cubic_shell_exact(N: int, parity: str) -> sp.Matrix:
    """Lean's intrinsicCubicShellPart, represented in ambient coordinates."""
    if N < 1:
        raise ValueError("require N>=1")
    s = exact_shell_generator(N, parity)
    g = successor_parity_cubic_vector_exact(N, parity)
    den = (s.T * s)[0]
    num = (s.T * g)[0]
    if den == 0 or num == 0:
        raise AssertionError("canonical cubic shell normalization degenerated")
    c = sp.simplify((num / den) * s)
    W = centered_predecessor_basis(N, parity)
    if W.T * c != sp.zeros(W.cols, 1):
        raise AssertionError("canonical cubic shell escaped W-perp")
    if g - c == sp.zeros(g.rows, 1):
        # Allowed mathematically, but keep this explicit for debugging.
        pass
    return c


def _coordinates_in_basis(B: sp.Matrix, v: sp.Matrix) -> sp.Matrix:
    if B.cols == 0:
        if v != sp.zeros(B.rows, 1):
            raise AssertionError("nonzero vector cannot lie in zero-dimensional basis")
        return sp.zeros(0, 1)
    sol, params = B.gauss_jordan_solve(v)
    if params.rows != 0:
        raise AssertionError("basis coordinates were not unique")
    if B * sol != v:
        raise AssertionError("basis membership check failed")
    return sol


@dataclass(frozen=True)
class ExactGeometry:
    N: int
    K: int
    W_plus: sp.Matrix
    W_minus: sp.Matrix
    c_plus: sp.Matrix
    c_minus: sp.Matrix
    g_minus: sp.Matrix
    d: sp.Matrix
    a: sp.Matrix
    d_coords: sp.Matrix
    a_coords: sp.Matrix


def biregular_zero_shift_geometry_exact(N: int) -> ExactGeometry:
    if N < 1:
        raise ValueError("require N>=1")
    K = N + 1
    W_plus = centered_predecessor_basis(N, "even")
    W_minus = centered_predecessor_basis(N, "odd")
    c_plus = canonical_cubic_shell_exact(N, "even")
    c_minus = canonical_cubic_shell_exact(N, "odd")
    g_minus = successor_parity_cubic_vector_exact(N, "odd")
    D = sp.diag(*_centered_indices(K))
    d = sp.simplify(D * c_plus - c_minus)
    a = sp.simplify(g_minus - c_minus)
    d_coords = _coordinates_in_basis(W_minus, d)
    a_coords = _coordinates_in_basis(W_minus, a)

    if D * c_plus != d + c_minus:
        raise AssertionError("D(c_plus)=d+c_minus failed")
    if g_minus != a + c_minus:
        raise AssertionError("g_minus=a+c_minus failed")
    return ExactGeometry(
        N=N,
        K=K,
        W_plus=W_plus,
        W_minus=W_minus,
        c_plus=c_plus,
        c_minus=c_minus,
        g_minus=g_minus,
        d=d,
        a=a,
        d_coords=d_coords,
        a_coords=a_coords,
    )


def centered_quadratic_normal_exact(K: int) -> sp.Matrix:
    ones = _power_vector(K, 0)
    d2 = _power_vector(K, 2)
    coeff = (ones.T * d2)[0] / (ones.T * ones)[0]
    n2 = sp.simplify(d2 - coeff * ones)
    if n2 == sp.zeros(2 * K + 1, 1):
        raise AssertionError("quadratic normal vanished")
    return n2


def _dot_arb(x: arb_mat, y: arb_mat) -> arb:
    if x.ncols() != 1 or y.ncols() != 1 or x.nrows() != y.nrows():
        raise ValueError("dot product expects equal column vectors")
    return (x.transpose() * y)[0, 0]


def _mat_vec_energy(M: arb_mat, v: arb_mat) -> arb:
    return (v.transpose() * M * v)[0, 0]


def positive_definite_record(H: arb_mat) -> dict[str, Any]:
    minors = principal_determinants_arb(H)
    certified = all(definitely_positive(x) for x in minors)
    return {
        "certified": certified,
        "leading_principal_minors": [ball_record(x) for x in minors],
    }


def zero_shift_response_record(M: arb_mat, W: sp.Matrix, c: sp.Matrix) -> dict[str, Any]:
    Wb = arb_matrix_from_sympy_rational(W)
    cb = arb_matrix_from_sympy_rational(c)
    A = Wb.transpose() * M * Wb if W.cols else arb_mat(0, 0)
    b = Wb.transpose() * M * cb if W.cols else arb_mat(0, 1)
    pd = positive_definite_record(A)

    if W.cols:
        if not pd["certified"]:
            raise ArithmeticError("predecessor block is not rigorously positive definite")
        y = A.solve(b)
        xb = Wb * y
    else:
        y = arb_mat(0, 1)
        xb = arb_mat([[arb(0)] for _ in range(c.rows)])

    ub = cb - xb
    shell_norm_sq = _dot_arb(cb, cb)
    if shell_norm_sq.contains(0):
        raise ArithmeticError("canonical shell norm enclosure contains zero")

    q = _mat_vec_energy(M, cb)
    schur = q - (_dot_arb(b, y) if W.cols else arb(0))
    sigma = schur / shell_norm_sq
    direct_energy = _mat_vec_energy(M, ub)
    sigma_direct = direct_energy / shell_norm_sq
    sigma_residual = sigma - sigma_direct

    return {
        "A": A,
        "b": b,
        "y": y,
        "x": xb,
        "u": ub,
        "predecessor_pd": pd,
        "shell_norm_sq": shell_norm_sq,
        "schur_endpoint": schur,
        "sigma": sigma,
        "direct_trial_energy": direct_energy,
        "sigma_direct": sigma_direct,
        "sigma_identity_residual": sigma_residual,
        "sigma_identity_overlap": bool(sigma_residual.contains(0)),
    }


def explicit_source_moment_from_matrix(M: arb_mat, u_plus: arb_mat, K: int) -> arb:
    n2 = arb_matrix_from_sympy_rational(centered_quadratic_normal_exact(K))
    den = _dot_arb(n2, n2)
    if den.contains(0):
        raise ArithmeticError("quadratic-normal denominator contains zero")
    return (n2.transpose() * M * u_plus)[0, 0] / den


def transfer_coefficients(x_minus: arb_mat, u_minus: arb_mat, geom: ExactGeometry) -> dict[str, arb]:
    cb = arb_matrix_from_sympy_rational(geom.c_minus)
    db = arb_matrix_from_sympy_rational(geom.d)
    ab = arb_matrix_from_sympy_rational(geom.a)
    gb = arb_matrix_from_sympy_rational(geom.g_minus)
    den = _dot_arb(cb, cb)
    if den.contains(0):
        raise ArithmeticError("odd shell norm contains zero")

    alpha0 = arb(1) - _dot_arb(x_minus, db) / den
    gamma0 = arb(1) - _dot_arb(x_minus, ab) / den
    gamma_overlap = _dot_arb(u_minus, gb) / den
    return {
        "alpha0": alpha0,
        "gamma0": gamma0,
        "gamma_overlap": gamma_overlap,
        "gamma_residual": gamma0 - gamma_overlap,
    }


def full_successor_pd_record(M: arb_mat, K: int, parity: str) -> dict[str, Any]:
    V = exact_parity_basis(K, parity)
    Vb = _arb_matrix_from_sympy(V)
    H = Vb.transpose() * M * Vb if V.cols else arb_mat(0, 0)
    rec = positive_definite_record(H)
    rec["dimension"] = V.cols
    return rec


def _scale_column(v: arb_mat, a: arb) -> arb_mat:
    if v.ncols() != 1:
        raise ValueError("expected column vector")
    return arb_mat([[a * v[i, 0]] for i in range(v.nrows())])


def transported_vector_residual(
    M: arb_mat,
    plus: dict[str, Any],
    geom: ExactGeometry,
    sigma_plus: arb,
    mu0: arb,
) -> tuple[arb_mat, bool]:
    """Check the exact compressed transport identity.

    Lean's left side is parityCompressedCanonical .odd, not the raw ambient
    matrix action.  Therefore we apply the exact Euclidean orthogonal
    projection onto the odd boundary-flat carrier after M(D u_+).
    """
    K = geom.K
    D = arb_matrix_from_sympy_rational(sp.diag(*_centered_indices(K)))
    du = D * plus["u"]

    Vodd = exact_parity_basis(K, "odd")
    gram = Vodd.T * Vodd
    if gram.det() == 0:
        raise AssertionError("odd successor carrier Gram matrix singular")
    Podd_exact = sp.simplify(Vodd * gram.inv() * Vodd.T)
    Podd = arb_matrix_from_sympy_rational(Podd_exact)
    lhs = Podd * (M * du)

    db = arb_matrix_from_sympy_rational(geom.d)
    ab = arb_matrix_from_sympy_rational(geom.a)
    cb = arb_matrix_from_sympy_rational(geom.c_minus)
    rhs = (
        _scale_column(db, sigma_plus)
        + _scale_column(ab, mu0)
        + _scale_column(cb, sigma_plus + mu0)
    )
    residual = lhs - rhs
    ok = all(bool(residual[i, 0].contains(0)) for i in range(residual.nrows()))
    return residual, ok


def _vector_ball_record(v: arb_mat) -> list[dict]:
    return [ball_record(v[i, 0]) for i in range(v.nrows())]


def classify_scalar(x: arb) -> str:
    if definitely_negative(x):
        return "SIGMA_MINUS_NEGATIVE_CERTIFIED"
    if definitely_positive(x):
        return "SIGMA_MINUS_POSITIVE_CERTIFIED"
    return "SIGMA_MINUS_SIGN_UNRESOLVED"


def biregular_zero_shift_scalar_record_arb(
    Q: int,
    t_num: int,
    t_den: int,
    N: int = 2,
) -> dict[str, Any]:
    if not (0 < t_num < t_den):
        raise ValueError("point must lie strictly inside the cutoff cell")
    t = arb(t_num) / t_den
    L = cell_coordinate_L_arb(Q, t)
    K = N + 1
    M = fixed_q_canonical_source_matrix_arb(L, K, Q)
    geom = biregular_zero_shift_geometry_exact(N)

    plus = zero_shift_response_record(M, geom.W_plus, geom.c_plus)
    minus = zero_shift_response_record(M, geom.W_minus, geom.c_minus)
    if not plus["sigma_identity_overlap"] or not minus["sigma_identity_overlap"]:
        raise AssertionError("direct-energy / Schur response identity mismatch")

    mu0 = explicit_source_moment_from_matrix(M, plus["u"], K)
    coeff = transfer_coefficients(minus["x"], minus["u"], geom)
    if not coeff["gamma_residual"].contains(0):
        raise AssertionError("Gamma overlap reconstruction mismatch")

    transferred = coeff["alpha0"] * plus["sigma"] + coeff["gamma0"] * mu0
    transfer_residual = minus["sigma"] - transferred
    if not transfer_residual.contains(0):
        raise AssertionError("zero-shift scalar transfer identity mismatch")

    vector_residual, vector_ok = transported_vector_residual(
        M, plus, geom, plus["sigma"], mu0
    )
    if not vector_ok:
        raise AssertionError("full transported-vector identity mismatch")

    odd_full = full_successor_pd_record(M, K, "odd")
    sigma_class = classify_scalar(minus["sigma"])
    if sigma_class == "SIGMA_MINUS_POSITIVE_CERTIFIED" and not odd_full["certified"]:
        raise AssertionError("positive Schur response disagrees with odd full-successor PD")
    if sigma_class == "SIGMA_MINUS_NEGATIVE_CERTIFIED" and not definitely_negative(
        minus["direct_trial_energy"]
    ):
        raise AssertionError("negative sigma does not produce negative odd trial energy")

    return {
        "Q": Q,
        "t_num": t_num,
        "t_den": t_den,
        "t": ball_record(t),
        "L": ball_record(L),
        "N": N,
        "Kstar": K,
        "geometry": {
            "c_plus": [str(_q(x)) for x in geom.c_plus],
            "c_minus": [str(_q(x)) for x in geom.c_minus],
            "d": [str(_q(x)) for x in geom.d],
            "a": [str(_q(x)) for x in geom.a],
            "D_c_plus_eq_d_plus_c_minus": True,
            "g_minus_eq_a_plus_c_minus": True,
        },
        "even": {
            "predecessor_pd": plus["predecessor_pd"],
            "sigma": ball_record(plus["sigma"]),
            "schur_endpoint": ball_record(plus["schur_endpoint"]),
            "direct_trial_energy": ball_record(plus["direct_trial_energy"]),
            "sigma_identity_residual": ball_record(plus["sigma_identity_residual"]),
        },
        "odd": {
            "predecessor_pd": minus["predecessor_pd"],
            "sigma": ball_record(minus["sigma"]),
            "schur_endpoint": ball_record(minus["schur_endpoint"]),
            "direct_trial_energy": ball_record(minus["direct_trial_energy"]),
            "sigma_identity_residual": ball_record(minus["sigma_identity_residual"]),
            "full_successor_pd": odd_full,
        },
        "transfer": {
            "alpha0": ball_record(coeff["alpha0"]),
            "Gamma0": ball_record(coeff["gamma0"]),
            "Gamma0_overlap": ball_record(coeff["gamma_overlap"]),
            "Gamma0_residual": ball_record(coeff["gamma_residual"]),
            "mu0": ball_record(mu0),
            "transferred_sigma_minus": ball_record(transferred),
            "scalar_residual": ball_record(transfer_residual),
            "vector_residual": _vector_ball_record(vector_residual),
            "vector_identity_overlap": vector_ok,
        },
        "sigma_plus_negative_certified": definitely_negative(plus["sigma"]),
        "sigma_minus_classification": sigma_class,
        "claim_cap": "RIGOROUS_FINITE_POINT_ZERO_SHIFT_SCALAR_AUDIT_ONLY",
    }
