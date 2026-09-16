#!/usr/bin/env python3
"""Canonical fixed-unit second aperture derivatives for the post-#194 Q14 trajectory audit.

This module extends the already-validated post-#177 fixed-unit derivative backend
from (M, M') to (M, M', M'') without changing the canonical source:

    M(L) = pole(L) - arch(L) - prime(L).

All second derivatives are analytic fixed-Q aperture derivatives.  The
archimedean scale is differentiated in a removable form, the pole term is
differentiated exactly, and the fixed-Q prime sum differentiates the existing
q_basis with the cutoff held fixed inside the certified physical cell.

Research/audit tooling only.  Finite-difference checks validate the
implementation but are not theorem authority.  RH remains OPEN.
"""
from __future__ import annotations

from flint import acb, arb, arb_mat

from canonical_source_arb import (
    _cos_slope,
    _exp_slope,
    _integral_real,
    _regularized_arch_scale,
    _sinh_slope,
    ball_record,
    direct_arch_component,
    pole_component,
    prime_component,
    von_mangoldt,
)
from post166_fb05_cell_interval import _arb_matrix_from_sympy
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import TARGET_KSTAR, TARGET_N, scalar_geometry
from post175_fb05_q13_fixed_unit_enclosure import fixed_unit_primitive_caches
from post177_fb05_q13_fixed_unit_derivative import (
    SUPPORTED_QS,
    ZERO_WEIGHT_DERIVATIVE_SEAMS,
    direct_arch_component_prime,
    fixed_unit_fixed_q_canonical_source_matrix_with_derivative_arb,
    fixed_unit_primitive_derivative_caches,
    pole_component_prime,
    prime_component_prime,
    q_basis_prime,
    regularized_arch_scale_L_derivative,
)


def _unit_integral_real(func) -> arb:
    return _integral_real(func, arb(1))


def regularized_arch_scale_L_second_derivative(L: arb, t: acb) -> acb:
    """Exact removable second derivative d²/dL² R(L*t).

    With z=L*t, S(z)=sinh(z)/z and
      R_L = R(z) * B(z) / L,
      B(z)=1+z/2-cosh(z)/S(z),
    one has
      R_LL = R(z)/L² * (B² - B + z B'),
    where
      z B' = z/2 - z² + cosh(z)*(cosh(z)-S(z))/S(z)².

    No division by z is introduced.
    """
    Lc = acb(L)
    z = Lc * t
    scale = _regularized_arch_scale(z)
    slope = _sinh_slope(z)
    cosh_z = z.cosh()
    B = acb(1) + z / 2 - cosh_z / slope
    zBprime = z / 2 - z * z + cosh_z * (cosh_z - slope) / (slope * slope)
    return scale * (B * B - B + zBprime) / (Lc * Lc)


def fixed_unit_alpha_L_second(n: int, L: arb) -> arb:
    two_pi_n = acb(2 * arb.pi() * n)
    return arb(2 * n) * _unit_integral_real(
        lambda t: (two_pi_n * t).sinc()
        * regularized_arch_scale_L_second_derivative(L, t)
    )


def fixed_unit_beta_L_second(n: int, L: arb) -> arb:
    two_pi_n = acb(2 * arb.pi() * n)
    return _unit_integral_real(
        lambda t: (two_pi_n * t).cos()
        * regularized_arch_scale_L_second_derivative(L, t)
    )


def w_correction_second(L: arb) -> arb:
    s = L.sinh()
    return -L.cosh() / (2 * s * s)


def fixed_unit_source_eq44_gamma_L_second(n: int, L: arb) -> arb:
    """Second derivative of the exact fixed-unit equation-(4.4) gamma primitive."""
    two_pi_n = acb(2 * arb.pi() * n)
    Lc = acb(L)

    def integrand(t: acb) -> acb:
        z = Lc * t
        scale = _regularized_arch_scale(z)
        scale_prime = regularized_arch_scale_L_derivative(L, t)
        scale_second = regularized_arch_scale_L_second_derivative(L, t)
        coeff = two_pi_n * _cos_slope(two_pi_n * t) + (Lc / 2) * _exp_slope(-z / 2)
        exp_half = (-z / 2).exp()
        coeff_prime = acb(arb(1) / 2) * exp_half
        coeff_second = -(t / 4) * exp_half
        return (
            coeff_second * scale
            + 2 * coeff_prime * scale_prime
            + coeff * scale_second
        )

    return _unit_integral_real(integrand) + w_correction_second(L)


def fixed_unit_primitive_second_derivative_caches(L: arb, N: int) -> dict:
    if N < 0:
        raise ValueError("require N>=0")
    idx = list(range(-N, N + 1))
    return {
        "alpha": {n: fixed_unit_alpha_L_second(n, L) for n in idx},
        "beta": {n: fixed_unit_beta_L_second(n, L) for n in idx},
        "gamma": {n: fixed_unit_source_eq44_gamma_L_second(n, L) for n in idx},
    }


def direct_arch_component_second(
    n: int,
    m: int,
    alpha_second: dict[int, arb],
    beta_second: dict[int, arb],
    gamma_second: dict[int, arb],
) -> arb:
    if n != m:
        return (alpha_second[m] - alpha_second[n]) / (n - m)
    return 2 * gamma_second[n] - 2 * beta_second[n]


def pole_component_second(n: int, m: int, L: arb) -> arb:
    """Exact second aperture derivative of canonical_source_arb.pole_component."""
    pi = arb.pi()
    s = (L / 4).sinh()
    c = (L / 4).cosh()
    a = 16 * pi ** 2 * m * n
    bm = 16 * pi ** 2 * m ** 2
    bn = 16 * pi ** 2 * n ** 2

    ls2 = L * s ** 2
    ls2_prime = s ** 2 + (L / 2) * s * c
    ls2_second = s * c + (L / 8) * (c ** 2 + s ** 2)

    q = L ** 2 - a
    q_prime = 2 * L
    q_second = arb(2)
    U = ls2 * q
    U_prime = ls2_prime * q + ls2 * q_prime
    U_second = ls2_second * q + 2 * ls2_prime * q_prime + ls2 * q_second

    dm = L ** 2 + bm
    dn = L ** 2 + bn
    D = dm * dn
    D_prime = 2 * L * (dm + dn)
    D_second = 2 * (dm + dn) + 8 * L ** 2

    return 32 * (
        U_second * D ** 2
        - U * D_second * D
        - 2 * U_prime * D * D_prime
        + 2 * U * D_prime ** 2
    ) / (D ** 3)


def q_basis_second(n: int, m: int, y: arb, L: arb) -> arb:
    """Exact fixed-y second aperture derivative of the production q_basis."""
    pi = arb.pi()
    x = y / L
    xp_sq = x * x / (L * L)
    x_second = 2 * x / (L * L)

    if n == m:
        A = 2 * pi * n
        Ax = A * x
        q_x = -2 * Ax.cos() - 2 * A * (1 - x) * Ax.sin()
        q_xx = 4 * A * Ax.sin() - 2 * A ** 2 * (1 - x) * Ax.cos()
    else:
        A = 2 * pi * n
        B = 2 * pi * m
        Ax = A * x
        Bx = B * x
        den = pi * (m - n)
        q_x = (A * Ax.cos() - B * Bx.cos()) / den
        q_xx = (-A ** 2 * Ax.sin() + B ** 2 * Bx.sin()) / den

    return q_xx * xp_sq + q_x * x_second


def prime_component_second(n: int, m: int, L: arb, Q: int) -> arb:
    total = arb(0)
    for k in range(2, Q + 1):
        vm = von_mangoldt(k)
        if vm.is_zero():
            continue
        y = arb(k).log()
        total += vm / arb(k).sqrt() * q_basis_second(n, m, y, L)
    return total


def fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(
    L: arb,
    N: int,
    Q: int,
) -> tuple[arb_mat, arb_mat, arb_mat]:
    """Return the complete fixed-Q canonical (M, M', M'')."""
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")

    M, Mprime = fixed_unit_fixed_q_canonical_source_matrix_with_derivative_arb(L, N, Q)
    idx = list(range(-N, N + 1))
    seconds = fixed_unit_primitive_second_derivative_caches(L, N)
    d2rows = [[arb(0) for _ in idx] for _ in idx]

    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            arch_second = direct_arch_component_second(
                n,
                m,
                seconds["alpha"],
                seconds["beta"],
                seconds["gamma"],
            )
            value_second = (
                pole_component_second(n, m, L)
                - arch_second
                - prime_component_second(n, m, L, Q)
            )
            d2rows[r][c] = d2rows[c][r] = value_second

    return M, Mprime, arb_mat(d2rows)


def _restrict_triple(
    M: arb_mat,
    Mprime: arb_mat,
    Msecond: arb_mat,
    parity: str,
) -> tuple[arb_mat, arb_mat, arb_mat, object]:
    geom = one_step_geometry(TARGET_N, parity)
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * M * B
    Hprime = B.transpose() * Mprime * B
    Hsecond = B.transpose() * Msecond * B
    if H.nrows() != 2 or H.ncols() != 2:
        raise AssertionError("unexpected fixed-unit second-derivative restriction dimension")
    return H, Hprime, Hsecond, scalar_geometry(parity)


def _scalar_with_second_derivative(
    H: arb_mat,
    Hprime: arb_mat,
    Hsecond: arb_mat,
    norms,
) -> dict:
    a = H[0, 0]
    b = H[0, 1]
    d = H[1, 1]
    ap = Hprime[0, 0]
    bp = Hprime[0, 1]
    dp = Hprime[1, 1]
    app = Hsecond[0, 0]
    bpp = Hsecond[0, 1]
    dpp = Hsecond[1, 1]

    delta2 = a * d - b * b
    delta2p = ap * d + a * dp - 2 * b * bp
    delta2pp = app * d + 2 * ap * dp + a * dpp - 2 * bp * bp - 2 * b * bpp

    return {
        "a": a,
        "b": b,
        "d": d,
        "delta2": delta2,
        "a_prime": ap,
        "b_prime": bp,
        "d_prime": dp,
        "delta2_prime": delta2p,
        "a_second": app,
        "b_second": bpp,
        "d_second": dpp,
        "delta2_second": delta2pp,
        "normalized_a": a / norms.W_norm_sq,
        "normalized_delta2": delta2 / (norms.W_norm_sq * norms.c_norm_sq),
        "normalized_a_prime": ap / norms.W_norm_sq,
        "normalized_delta2_prime": delta2p / (norms.W_norm_sq * norms.c_norm_sq),
        "normalized_a_second": app / norms.W_norm_sq,
        "normalized_delta2_second": delta2pp / (norms.W_norm_sq * norms.c_norm_sq),
    }


def fixed_unit_second_derivative_scalar_record_arb_at_L(Q: int, L: arb) -> dict:
    if Q not in SUPPORTED_QS:
        raise ValueError(f"fixed-unit second derivative helper supports Q in {SUPPORTED_QS}")

    M, Mprime, Msecond = (
        fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(
            L, TARGET_KSTAR, Q
        )
    )
    He, Hep, Hepp, ne = _restrict_triple(M, Mprime, Msecond, "even")
    Ho, Hop, Hopp, no = _restrict_triple(M, Mprime, Msecond, "odd")
    even = _scalar_with_second_derivative(He, Hep, Hepp, ne)
    odd = _scalar_with_second_derivative(Ho, Hop, Hopp, no)

    return {
        "Q": int(Q),
        "L": L,
        "matrix": M,
        "matrix_prime": Mprime,
        "matrix_second": Msecond,
        "even_H": He,
        "even_H_prime": Hep,
        "even_H_second": Hepp,
        "odd_H": Ho,
        "odd_H_prime": Hop,
        "odd_H_second": Hopp,
        "even": even,
        "odd_N2_predecessor": odd["a"],
        "odd_N2_predecessor_prime": odd["a_prime"],
        "odd_N2_predecessor_second": odd["a_second"],
        "odd_N2_predecessor_normalized": odd["normalized_a"],
        "odd_N2_predecessor_normalized_prime": odd["normalized_a_prime"],
        "odd_N2_predecessor_normalized_second": odd["normalized_a_second"],
    }


def second_derivative_seam_overlap_record(k: int) -> dict:
    """Check M'' continuation only at the inherited zero-von-Mangoldt seams."""
    if k not in ZERO_WEIGHT_DERIVATIVE_SEAMS:
        raise ValueError(
            f"second derivative seam check only valid for {ZERO_WEIGHT_DERIVATIVE_SEAMS}"
        )
    L = arb(k).log()
    left = fixed_unit_second_derivative_scalar_record_arb_at_L(k - 1, L)
    right = fixed_unit_second_derivative_scalar_record_arb_at_L(k, L)

    def overlap(x: arb, y: arb) -> bool:
        return bool((x - y).contains(0))

    matrix_second_overlap = all(
        overlap(left["matrix_second"][r, c], right["matrix_second"][r, c])
        for r in range(left["matrix_second"].nrows())
        for c in range(left["matrix_second"].ncols())
    )
    fields = {
        "even_a_second": (left["even"]["a_second"], right["even"]["a_second"]),
        "even_b_second": (left["even"]["b_second"], right["even"]["b_second"]),
        "even_d_second": (left["even"]["d_second"], right["even"]["d_second"]),
        "even_delta2_second": (
            left["even"]["delta2_second"],
            right["even"]["delta2_second"],
        ),
        "odd_N2_predecessor_second": (
            left["odd_N2_predecessor_second"],
            right["odd_N2_predecessor_second"],
        ),
    }
    overlaps = {name: overlap(a, b) for name, (a, b) in fields.items()}
    return {
        "k": int(k),
        "L": ball_record(L),
        "left_Q": int(k - 1),
        "right_Q": int(k),
        "matrix_second_all_entries_overlap": matrix_second_overlap,
        "scalar_second_derivative_overlaps": overlaps,
        "all_overlap": matrix_second_overlap and all(overlaps.values()),
    }
