#!/usr/bin/env python3
"""Rigorous Arb/FLINT backend for the production canonical CCM source.

Unlike the fast discovery backend, this module does not import the legacy R004
matrix builder.  It reconstructs the *direct* equation-(4.4) canonical source
from the repository formulas using Arb real/complex ball arithmetic.

The origin-sensitive archimedean integrands are evaluated in the removable
forms theoremized by ``CanonicalApertureContinuity.lean``.  This avoids treating
repeated high precision as certification: every returned ``arb``/``arb_mat``
object is an enclosure.

The prime sum is frozen by an explicitly certified physical cutoff cell
``log Q < L < log(Q+1)``.
"""
from __future__ import annotations

from typing import Callable

import sympy as sp
from flint import acb, arb, arb_mat, ctx, fmpq

I = acb(0, 1)


def set_precision(bits: int = 192) -> None:
    if bits < 80:
        raise ValueError("certification precision must be at least 80 bits")
    ctx.prec = bits


def to_arb_rational(num: int, den: int = 1) -> arb:
    if den <= 0:
        raise ValueError("denominator must be positive")
    return arb(fmpq(int(num), int(den)))


def definitely_positive(x: arb) -> bool:
    return bool(x > 0)


def definitely_negative(x: arb) -> bool:
    return bool(x < 0)


def definitely_nonzero(x: arb) -> bool:
    return not x.contains(0)


def ball_record(x: arb, digits: int = 30) -> dict:
    return {
        "ball": x.str(digits, more=True),
        "lower": x.lower().str(digits, radius=False),
        "upper": x.upper().str(digits, radius=False),
        "contains_zero": bool(x.contains(0)),
        "rel_accuracy_bits": int(x.rel_accuracy_bits()),
    }


def fixed_cell_membership(Q: int, L: arb) -> dict:
    if Q < 1:
        raise ValueError("require Q>=1")
    lo = arb(Q).log()
    hi = arb(Q + 1).log()
    lower_ok = bool(lo < L)
    upper_ok = bool(L < hi)
    return {
        "Q": Q,
        "lower": ball_record(lo),
        "L": ball_record(L),
        "upper": ball_record(hi),
        "certified": lower_ok and upper_ok,
    }


def _integral_real(func: Callable[[acb], acb], L: arb) -> arb:
    """Rigorous real integral on [0,L] via Arb's validated complex integrator."""
    result = acb.integral(lambda z, _analytic: func(z), acb(0), acb(L))
    if not result.imag.contains(0):
        raise ArithmeticError(f"real integral acquired non-real enclosure: {result}")
    return result.real


def _sinh_slope(z: acb) -> acb:
    # sinh(z)/z = sinc(i*z), including the removable value at z=0.
    return (I * z).sinc()


def _regularized_arch_scale(z: acb) -> acb:
    # exp(z/2) / (2 * (sinh(z)/z)).
    return (z / 2).exp() / (2 * _sinh_slope(z))


def _cos_slope(z: acb) -> acb:
    # (cos z - 1)/z = -(z/2) * sinc(z/2)^2.
    h = z / 2
    return -h * h.sinc() ** 2


def _exp_slope(z: acb) -> acb:
    # (exp z - 1)/z = exp(z/2) * sinh(z/2)/(z/2).
    h = z / 2
    return h.exp() * (I * h).sinc()


def _regularized_alpha_integrand(n: int, L: arb, z: acb) -> acb:
    a = acb(2 * arb.pi() * n / L)
    return a * (a * z).sinc() * _regularized_arch_scale(z)


def _regularized_beta_integrand(n: int, L: arb, z: acb) -> acb:
    a = acb(2 * arb.pi() * n / L)
    return (a * z).cos() * _regularized_arch_scale(z)


def _regularized_gamma_integrand(n: int, L: arb, z: acb) -> acb:
    a = acb(2 * arb.pi() * n / L)
    return (
        a * _cos_slope(a * z)
        + acb(arb(1) / 2) * _exp_slope(-z / 2)
    ) * _regularized_arch_scale(z)


def _regularized_c_correction_integrand(z: acb) -> acb:
    # (1-exp(-z/2))/(exp(z)-exp(-z)), with its removable value 1/4.
    return (
        (-z / 4).exp()
        * acb(arb(1) / 4)
        * (I * z / 4).sinc()
        / (I * z).sinc()
    )


def alpha_L(n: int, L: arb) -> arb:
    return _integral_real(lambda z: _regularized_alpha_integrand(n, L, z), L) / arb.pi()


def beta_L(n: int, L: arb) -> arb:
    return _integral_real(lambda z: _regularized_beta_integrand(n, L, z), L) / L


def source_eq44_gamma_L(n: int, L: arb) -> arb:
    """Direct production gamma primitive: regularized (4.11)-lhs integral + w."""
    return _integral_real(lambda z: _regularized_gamma_integrand(n, L, z), L) + w_correction(L)


def c_correction(L: arb) -> arb:
    return _integral_real(_regularized_c_correction_integrand, L)


def w_correction(L: arb) -> arb:
    eL = L.exp()
    ratio = (eL + 1) / (eL - 1)
    return (arb.const_euler() + (4 * arb.pi()).log()) / 2 - ratio.log() / 2


def pole_component(n: int, m: int, L: arb) -> arb:
    pi = arb.pi()
    num = 32 * L * (L / 4).sinh() ** 2 * (L ** 2 - 16 * pi ** 2 * m * n)
    den = (L ** 2 + 16 * pi ** 2 * m ** 2) * (L ** 2 + 16 * pi ** 2 * n ** 2)
    return num / den


def q_basis(n: int, m: int, y: arb, L: arb) -> arb:
    pi = arb.pi()
    if n == m:
        return 2 * (1 - y / L) * (2 * pi * n * y / L).cos()
    return ((2 * pi * n * y / L).sin() - (2 * pi * m * y / L).sin()) / (pi * (m - n))


def von_mangoldt(k: int) -> arb:
    if k < 2:
        return arb(0)
    fac = sp.factorint(int(k))
    if len(fac) != 1:
        return arb(0)
    p = next(iter(fac))
    return arb(int(p)).log()


def prime_component(n: int, m: int, L: arb, Q: int) -> arb:
    total = arb(0)
    for k in range(2, Q + 1):
        vm = von_mangoldt(k)
        if vm.is_zero():
            continue
        total += vm / arb(k).sqrt() * q_basis(n, m, arb(k).log(), L)
    return total


def direct_arch_component(
    n: int,
    m: int,
    L: arb,
    alpha_cache: dict[int, arb],
    beta_cache: dict[int, arb],
    gamma_cache: dict[int, arb],
) -> arb:
    if n != m:
        return (alpha_cache[m] - alpha_cache[n]) / (n - m)
    return 2 * gamma_cache[n] - 2 * beta_cache[n]


def canonical_source_matrix(L: arb, N: int, Q: int) -> arb_mat:
    """Rigorous direct-production canonicalSourceMatrix enclosure."""
    if N < 0:
        raise ValueError("require N>=0")
    membership = fixed_cell_membership(Q, L)
    if not membership["certified"]:
        raise ValueError("aperture is not certified inside the requested cutoff cell")

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


def signed_channel_matrices(L: arb, N: int, Q: int) -> dict[str, arb_mat]:
    """Canonical source split in legacy+repair coordinates.

    canonical = pole - legacy_arch - prime + 2*cCorrection(L) I.
    """
    if N < 0:
        raise ValueError("require N>=0")
    membership = fixed_cell_membership(Q, L)
    if not membership["certified"]:
        raise ValueError("aperture is not certified inside the requested cutoff cell")

    idx = list(range(-N, N + 1))
    dim = len(idx)
    alpha_cache = {n: alpha_L(n, L) for n in idx}
    beta_cache = {n: beta_L(n, L) for n in idx}
    gamma_direct = {n: source_eq44_gamma_L(n, L) for n in idx}
    cc = c_correction(L)

    pole_rows = [[arb(0) for _ in idx] for _ in idx]
    arch_rows = [[arb(0) for _ in idx] for _ in idx]
    prime_rows = [[arb(0) for _ in idx] for _ in idx]

    for r, n in enumerate(idx):
        for c in range(r, dim):
            m = idx[c]
            pole = pole_component(n, m, L)
            arch_direct = direct_arch_component(n, m, L, alpha_cache, beta_cache, gamma_direct)
            arch_legacy = arch_direct + (2 * cc if n == m else 0)
            prime = prime_component(n, m, L, Q)
            pole_rows[r][c] = pole_rows[c][r] = pole
            arch_rows[r][c] = arch_rows[c][r] = -arch_legacy
            prime_rows[r][c] = prime_rows[c][r] = -prime

    scalar_rows = [[2 * cc if r == c else arb(0) for c in range(dim)] for r in range(dim)]
    return {
        "pole": arb_mat(pole_rows),
        "arch_signed": arb_mat(arch_rows),
        "prime_signed": arb_mat(prime_rows),
        "scalar_shift": arb_mat(scalar_rows),
    }


def channel_reconstruction(L: arb, N: int, Q: int) -> tuple[arb_mat, arb_mat]:
    direct = canonical_source_matrix(L, N, Q)
    channels = signed_channel_matrices(L, N, Q)
    rebuilt = channels["pole"] + channels["arch_signed"] + channels["prime_signed"] + channels["scalar_shift"]
    return direct, rebuilt
