#!/usr/bin/env python3
"""Fixed-unit aperture derivatives for the post-#177 FB-05 q13/Q14 laboratory.

The value representation was selected by research PR #176.  This module keeps
that fixed-unit representation and differentiates the *complete* fixed-Q
canonical source

    M(L) = pole(L) - arch(L) - prime(L).

The oscillatory phase in the fixed-unit archimedean primitives is independent
of L.  The only new analytic ingredient is the removable L-derivative of the
regularized scale R(L t).  Pole and fixed-Q prime derivatives are included
explicitly; differentiating only the archimedean channel would not be the
canonical derivative.

Research/audit tooling only.  No output here is Lean theorem authority.
RH remains OPEN.
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
from post166_fb05_cell_interval import _arb_matrix_from_sympy, arb_unit_interval, cell_coordinate_L_arb
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import PHYSICAL_QS, TARGET_KSTAR, TARGET_N, scalar_geometry
from post175_fb05_q13_fixed_unit_enclosure import fixed_unit_primitive_caches

SUPPORTED_QS = (12, 13, 14, 15, 16)
ZERO_WEIGHT_DERIVATIVE_SEAMS = (14, 15)


def _unit_integral_real(func) -> arb:
    return _integral_real(func, arb(1))


def regularized_arch_scale_L_derivative(L: arb, t: acb) -> acb:
    """Exact removable derivative d/dL R(L*t) on the positive-aperture cells.

    For S(z)=sinh(z)/z and R(z)=exp(z/2)/(2*S(z)),

      z R'(z) = R(z) * (1 + z/2 - cosh(z)/S(z)).

    Hence d/dL R(L*t) is obtained without dividing by z=L*t.  Division is only
    by L, which is bounded away from zero on the q13/Q14 laboratory.
    """
    Lc = acb(L)
    z = Lc * t
    scale = _regularized_arch_scale(z)
    bracket = acb(1) + z / 2 - z.cosh() / _sinh_slope(z)
    return scale * bracket / Lc


def fixed_unit_alpha_L_prime(n: int, L: arb) -> arb:
    two_pi_n = acb(2 * arb.pi() * n)
    return arb(2 * n) * _unit_integral_real(
        lambda t: (two_pi_n * t).sinc() * regularized_arch_scale_L_derivative(L, t)
    )


def fixed_unit_beta_L_prime(n: int, L: arb) -> arb:
    two_pi_n = acb(2 * arb.pi() * n)
    return _unit_integral_real(
        lambda t: (two_pi_n * t).cos() * regularized_arch_scale_L_derivative(L, t)
    )


def w_correction_prime(L: arb) -> arb:
    """Exact derivative of the production wCorrection."""
    return arb(1) / (2 * L.sinh())


def fixed_unit_source_eq44_gamma_L_prime(n: int, L: arb) -> arb:
    """Derivative of the exact fixed-unit equation-(4.4) gamma primitive.

    If
      B(L,t)=2*pi*n*cosSlope(2*pi*n*t) + L/2*expSlope(-L*t/2),
    then
      dB/dL = (1/2)*exp(-L*t/2).
    """
    two_pi_n = acb(2 * arb.pi() * n)
    Lc = acb(L)

    def integrand(t: acb) -> acb:
        z = Lc * t
        scale = _regularized_arch_scale(z)
        scale_prime = regularized_arch_scale_L_derivative(L, t)
        coeff = two_pi_n * _cos_slope(two_pi_n * t) + (Lc / 2) * _exp_slope(-z / 2)
        coeff_prime = acb(arb(1) / 2) * (-z / 2).exp()
        return coeff_prime * scale + coeff * scale_prime

    return _unit_integral_real(integrand) + w_correction_prime(L)


def fixed_unit_primitive_derivative_caches(L: arb, N: int) -> dict:
    if N < 0:
        raise ValueError("require N>=0")
    idx = list(range(-N, N + 1))
    return {
        "alpha": {n: fixed_unit_alpha_L_prime(n, L) for n in idx},
        "beta": {n: fixed_unit_beta_L_prime(n, L) for n in idx},
        "gamma": {n: fixed_unit_source_eq44_gamma_L_prime(n, L) for n in idx},
    }


def direct_arch_component_prime(
    n: int,
    m: int,
    alpha_prime: dict[int, arb],
    beta_prime: dict[int, arb],
    gamma_prime: dict[int, arb],
) -> arb:
    if n != m:
        return (alpha_prime[m] - alpha_prime[n]) / (n - m)
    return 2 * gamma_prime[n] - 2 * beta_prime[n]


def pole_component_prime(n: int, m: int, L: arb) -> arb:
    """Analytic L-derivative of canonical_source_arb.pole_component."""
    pi = arb.pi()
    s = (L / 4).sinh()
    c = (L / 4).cosh()
    a = 16 * pi ** 2 * m * n
    bm = 16 * pi ** 2 * m ** 2
    bn = 16 * pi ** 2 * n ** 2

    ls2 = L * s ** 2
    ls2_prime = s ** 2 + (L / 2) * s * c
    q = L ** 2 - a
    q_prime = 2 * L
    U = ls2 * q
    U_prime = ls2_prime * q + ls2 * q_prime

    dm = L ** 2 + bm
    dn = L ** 2 + bn
    D = dm * dn
    D_prime = 2 * L * (dm + dn)
    return 32 * (U_prime * D - U * D_prime) / (D ** 2)


def q_basis_prime(n: int, m: int, y: arb, L: arb) -> arb:
    """Exact fixed-y aperture derivative of the production q_basis."""
    pi = arb.pi()
    x = y / L
    if n == m:
        kx = 2 * pi * n * x
        return (2 * x / L) * (kx.cos() + (1 - x) * (2 * pi * n) * kx.sin())
    nx = 2 * pi * n * x
    mx = 2 * pi * m * x
    numerator = 2 * pi * n * nx.cos() - 2 * pi * m * mx.cos()
    return -(x / L) * numerator / (pi * (m - n))


def prime_component_prime(n: int, m: int, L: arb, Q: int) -> arb:
    """Derivative of the fixed-Q prime channel inside one physical cutoff cell."""
    total = arb(0)
    for k in range(2, Q + 1):
        vm = von_mangoldt(k)
        if vm.is_zero():
            continue
        y = arb(k).log()
        total += vm / arb(k).sqrt() * q_basis_prime(n, m, y, L)
    return total


def fixed_unit_fixed_q_canonical_source_matrix_with_derivative_arb(
    L: arb,
    N: int,
    Q: int,
) -> tuple[arb_mat, arb_mat]:
    """Return the fixed-unit value matrix and complete fixed-Q L-derivative."""
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")
    idx = list(range(-N, N + 1))
    values = fixed_unit_primitive_caches(L, N)
    derivs = fixed_unit_primitive_derivative_caches(L, N)
    rows = [[arb(0) for _ in idx] for _ in idx]
    drows = [[arb(0) for _ in idx] for _ in idx]

    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            arch = direct_arch_component(
                n, m, L, values["alpha"], values["beta"], values["gamma"]
            )
            arch_prime = direct_arch_component_prime(
                n, m, derivs["alpha"], derivs["beta"], derivs["gamma"]
            )
            value = pole_component(n, m, L) - arch - prime_component(n, m, L, Q)
            derivative = (
                pole_component_prime(n, m, L)
                - arch_prime
                - prime_component_prime(n, m, L, Q)
            )
            rows[r][c] = rows[c][r] = value
            drows[r][c] = drows[c][r] = derivative
    return arb_mat(rows), arb_mat(drows)


def _restrict_pair(M: arb_mat, Mprime: arb_mat, parity: str) -> tuple[arb_mat, arb_mat, object]:
    geom = one_step_geometry(TARGET_N, parity)
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * M * B
    Hprime = B.transpose() * Mprime * B
    if H.nrows() != 2 or H.ncols() != 2:
        raise AssertionError("unexpected fixed-unit derivative restriction dimension")
    return H, Hprime, scalar_geometry(parity)


def _scalar_with_derivative(H: arb_mat, Hprime: arb_mat, norms) -> dict:
    a = H[0, 0]
    b = H[0, 1]
    d = H[1, 1]
    ap = Hprime[0, 0]
    bp = Hprime[0, 1]
    dp = Hprime[1, 1]
    delta2 = a * d - b * b
    delta2p = ap * d + a * dp - 2 * b * bp
    return {
        "a": a,
        "b": b,
        "d": d,
        "delta2": delta2,
        "a_prime": ap,
        "b_prime": bp,
        "d_prime": dp,
        "delta2_prime": delta2p,
        "normalized_a": a / norms.W_norm_sq,
        "normalized_delta2": delta2 / (norms.W_norm_sq * norms.c_norm_sq),
        "normalized_a_prime": ap / norms.W_norm_sq,
        "normalized_delta2_prime": delta2p / (norms.W_norm_sq * norms.c_norm_sq),
    }


def fixed_unit_derivative_scalar_record_arb_at_L(Q: int, L: arb) -> dict:
    if Q not in SUPPORTED_QS:
        raise ValueError(f"fixed-unit derivative helper supports Q in {SUPPORTED_QS}")
    M, Mprime = fixed_unit_fixed_q_canonical_source_matrix_with_derivative_arb(L, TARGET_KSTAR, Q)
    He, Hep, ne = _restrict_pair(M, Mprime, "even")
    Ho, Hop, no = _restrict_pair(M, Mprime, "odd")
    even = _scalar_with_derivative(He, Hep, ne)
    odd = _scalar_with_derivative(Ho, Hop, no)
    return {
        "Q": int(Q),
        "L": L,
        "matrix": M,
        "matrix_prime": Mprime,
        "even_H": He,
        "even_H_prime": Hep,
        "odd_H": Ho,
        "odd_H_prime": Hop,
        "even": even,
        "odd_N2_predecessor": odd["a"],
        "odd_N2_predecessor_prime": odd["a_prime"],
        "odd_N2_predecessor_normalized": odd["normalized_a"],
        "odd_N2_predecessor_normalized_prime": odd["normalized_a_prime"],
    }


def fixed_unit_derivative_scalar_interval_record_arb(
    Q: int,
    lo_num: int,
    hi_num: int,
    den: int,
) -> dict:
    if Q not in PHYSICAL_QS:
        raise ValueError(f"Q must be one of {PHYSICAL_QS}")
    t = arb_unit_interval(lo_num, hi_num, den)
    L = cell_coordinate_L_arb(Q, t)
    rec = fixed_unit_derivative_scalar_record_arb_at_L(Q, L)
    return {
        **rec,
        "t": t,
        "lo_num": int(lo_num),
        "hi_num": int(hi_num),
        "den": int(den),
    }


def _overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def derivative_seam_overlap_record(k: int) -> dict:
    """Derivative continuation check only at zero-von-Mangoldt seams 14 and 15."""
    if k not in ZERO_WEIGHT_DERIVATIVE_SEAMS:
        raise ValueError(f"derivative seam check only valid for {ZERO_WEIGHT_DERIVATIVE_SEAMS}")
    L = arb(k).log()
    left = fixed_unit_derivative_scalar_record_arb_at_L(k - 1, L)
    right = fixed_unit_derivative_scalar_record_arb_at_L(k, L)
    matrix_prime_overlap = all(
        _overlap(left["matrix_prime"][r, c], right["matrix_prime"][r, c])
        for r in range(left["matrix_prime"].nrows())
        for c in range(left["matrix_prime"].ncols())
    )
    fields = {
        "even_a_prime": (left["even"]["a_prime"], right["even"]["a_prime"]),
        "even_b_prime": (left["even"]["b_prime"], right["even"]["b_prime"]),
        "even_d_prime": (left["even"]["d_prime"], right["even"]["d_prime"]),
        "even_delta2_prime": (left["even"]["delta2_prime"], right["even"]["delta2_prime"]),
        "odd_N2_predecessor_prime": (
            left["odd_N2_predecessor_prime"], right["odd_N2_predecessor_prime"]
        ),
    }
    overlaps = {name: _overlap(a, b) for name, (a, b) in fields.items()}
    return {
        "k": int(k),
        "L": ball_record(L),
        "left_Q": int(k - 1),
        "right_Q": int(k),
        "matrix_prime_all_entries_overlap": matrix_prime_overlap,
        "scalar_derivative_overlaps": overlaps,
        "all_overlap": matrix_prime_overlap and all(overlaps.values()),
    }
