#!/usr/bin/env python3
"""Theorem-aligned full-composite parity-gap jets for post-#202 FB-05 research.

The exact PR #184 source decomposition is

    M_Q(L) = -log(L) I + R_Q(L),

where the real frozen remainder removes only the index-independent production
wCorrection from the archimedean channel.  The parity-gap contrast

    C_G = w_o w_o^T / ||w_o||^2 - w_e w_e^T / ||w_e||^2

has exact trace zero, so every scalar identity direction vanishes.  This module
therefore evaluates G, G', G'' from the scalar-free assembled canonical object

    pole - arch_without_w - frozen_prime

*before* interval transport.  The old independently assembled total M/M'/M''
path is retained only as a reconstruction check.

Research/audit tooling only.  No sign law is asserted here.  RH remains OPEN.
"""
from __future__ import annotations

import sympy as sp
from flint import acb, arb, arb_mat

from canonical_source_arb import (
    _cos_slope,
    _exp_slope,
    _integral_real,
    _regularized_arch_scale,
    ball_record,
    pole_component,
    prime_component,
)
from post166_fb05_cell_interval import _arb_matrix_from_sympy
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import TARGET_N, scalar_geometry
from post175_fb05_q13_fixed_unit_enclosure import fixed_unit_alpha_L, fixed_unit_beta_L
from post177_fb05_q13_fixed_unit_derivative import (
    fixed_unit_alpha_L_prime,
    fixed_unit_beta_L_prime,
    pole_component_prime,
    prime_component_prime,
    regularized_arch_scale_L_derivative,
)
from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_alpha_L_second,
    fixed_unit_beta_L_second,
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb,
    pole_component_second,
    prime_component_second,
    regularized_arch_scale_L_second_derivative,
)
from post198_fb05_q14_four_way_channel_second_derivative import matrix_all_entries_overlap


def _unit_integral_real(func) -> arb:
    return _integral_real(func, arb(1))


def fixed_unit_gamma_core(n: int, L: arb) -> arb:
    """Direct fixed-unit equation-(4.4) gamma primitive with wCorrection omitted."""
    two_pi_n = acb(2 * arb.pi() * n)
    Lc = acb(L)

    def integrand(t: acb) -> acb:
        z = Lc * t
        coeff = two_pi_n * _cos_slope(two_pi_n * t) + (Lc / 2) * _exp_slope(-z / 2)
        return coeff * _regularized_arch_scale(z)

    return _unit_integral_real(integrand)


def fixed_unit_gamma_core_prime(n: int, L: arb) -> arb:
    """First aperture derivative of the wCorrection-free gamma core."""
    two_pi_n = acb(2 * arb.pi() * n)
    Lc = acb(L)

    def integrand(t: acb) -> acb:
        z = Lc * t
        scale = _regularized_arch_scale(z)
        scale_prime = regularized_arch_scale_L_derivative(L, t)
        coeff = two_pi_n * _cos_slope(two_pi_n * t) + (Lc / 2) * _exp_slope(-z / 2)
        coeff_prime = acb(arb(1) / 2) * (-z / 2).exp()
        return coeff_prime * scale + coeff * scale_prime

    return _unit_integral_real(integrand)


def fixed_unit_gamma_core_second(n: int, L: arb) -> arb:
    """Second aperture derivative of the wCorrection-free gamma core."""
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
        return coeff_second * scale + 2 * coeff_prime * scale_prime + coeff * scale_second

    return _unit_integral_real(integrand)


def _primitive_caches(L: arb, N: int) -> tuple[dict, dict, dict]:
    idx = list(range(-N, N + 1))
    value = {
        "alpha": {n: fixed_unit_alpha_L(n, L) for n in idx},
        "beta": {n: fixed_unit_beta_L(n, L) for n in idx},
        "gamma": {n: fixed_unit_gamma_core(n, L) for n in idx},
    }
    first = {
        "alpha": {n: fixed_unit_alpha_L_prime(n, L) for n in idx},
        "beta": {n: fixed_unit_beta_L_prime(n, L) for n in idx},
        "gamma": {n: fixed_unit_gamma_core_prime(n, L) for n in idx},
    }
    second = {
        "alpha": {n: fixed_unit_alpha_L_second(n, L) for n in idx},
        "beta": {n: fixed_unit_beta_L_second(n, L) for n in idx},
        "gamma": {n: fixed_unit_gamma_core_second(n, L) for n in idx},
    }
    return value, first, second


def _arch_without_w_component(n: int, m: int, cache: dict) -> arb:
    if n != m:
        return (cache["alpha"][m] - cache["alpha"][n]) / (n - m)
    return 2 * cache["gamma"][n] - 2 * cache["beta"][n]


def scalar_free_full_composite_matrix_jets(L: arb, N: int, Q: int) -> dict:
    """Assemble pole - arch_without_w - prime through second aperture order."""
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")
    idx = list(range(-N, N + 1))
    value_cache, first_cache, second_cache = _primitive_caches(L, N)
    rows = [[arb(0) for _ in idx] for _ in idx]
    prows = [[arb(0) for _ in idx] for _ in idx]
    pprows = [[arb(0) for _ in idx] for _ in idx]

    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            value = (
                pole_component(n, m, L)
                - _arch_without_w_component(n, m, value_cache)
                - prime_component(n, m, L, Q)
            )
            first = (
                pole_component_prime(n, m, L)
                - _arch_without_w_component(n, m, first_cache)
                - prime_component_prime(n, m, L, Q)
            )
            second = (
                pole_component_second(n, m, L)
                - _arch_without_w_component(n, m, second_cache)
                - prime_component_second(n, m, L, Q)
            )
            rows[r][c] = rows[c][r] = value
            prows[r][c] = prows[c][r] = first
            pprows[r][c] = pprows[c][r] = second

    return {
        "matrix": arb_mat(rows),
        "matrix_prime": arb_mat(prows),
        "matrix_second": arb_mat(pprows),
    }


def exact_parity_gap_contrast_matrix() -> sp.Matrix:
    even = one_step_geometry(TARGET_N, "even").W_exact
    odd = one_step_geometry(TARGET_N, "odd").W_exact
    if even.cols != 1 or odd.cols != 1 or even.rows != odd.rows:
        raise AssertionError("post-#202 contrast requires one-dimensional shared predecessor carriers")
    even_sq = sp.expand((even.T * even)[0, 0])
    odd_sq = sp.expand((odd.T * odd)[0, 0])
    if int(even_sq) != int(scalar_geometry("even").W_norm_sq):
        raise AssertionError("even predecessor norm drift")
    if int(odd_sq) != int(scalar_geometry("odd").W_norm_sq):
        raise AssertionError("odd predecessor norm drift")
    contrast = odd * odd.T / odd_sq - even * even.T / even_sq
    if contrast.T != contrast:
        raise AssertionError("parity-gap contrast lost symmetry")
    if sp.simplify(contrast.trace()) != 0:
        raise AssertionError("parity-gap contrast lost exact trace-zero identity")
    if contrast == sp.zeros(contrast.rows, contrast.cols):
        raise AssertionError("parity-gap contrast collapsed to zero")
    return contrast


def parity_gap_contrast_metadata() -> dict:
    contrast = exact_parity_gap_contrast_matrix()
    return {
        "dimension": int(contrast.rows),
        "symmetric": contrast.T == contrast,
        "trace_zero": sp.simplify(contrast.trace()) == 0,
        "nonzero": contrast != sp.zeros(contrast.rows, contrast.cols),
        "even_norm_sq": int(scalar_geometry("even").W_norm_sq),
        "odd_norm_sq": int(scalar_geometry("odd").W_norm_sq),
    }


def _contract(matrix: arb_mat, contrast: arb_mat) -> arb:
    if matrix.nrows() != contrast.nrows() or matrix.ncols() != contrast.ncols():
        raise ValueError("contrast/matrix dimension mismatch")
    return sum(
        (contrast[r, c] * matrix[r, c] for r in range(matrix.nrows()) for c in range(matrix.ncols())),
        arb(0),
    )


def _overlap(left: arb, right: arb) -> bool:
    return bool((left - right).contains(0))


def parity_gap_contrast_jets(L: arb, N: int, Q: int) -> dict:
    """Evaluate G/G'/G'' with common scalar directions removed before transport."""
    contrast_exact = exact_parity_gap_contrast_matrix()
    if contrast_exact.rows != 2 * N + 1:
        raise ValueError("contrast dimension does not match requested canonical matrix size")
    contrast = _arb_matrix_from_sympy(contrast_exact)
    scalar_free = scalar_free_full_composite_matrix_jets(L, N, Q)
    G = _contract(scalar_free["matrix"], contrast)
    Gp = _contract(scalar_free["matrix_prime"], contrast)
    Gpp = _contract(scalar_free["matrix_second"], contrast)

    direct_M, direct_Mp, direct_Mpp = (
        fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(L, N, Q)
    )
    direct_G = _contract(direct_M, contrast)
    direct_Gp = _contract(direct_Mp, contrast)
    direct_Gpp = _contract(direct_Mpp, contrast)
    checks = {
        "G_direct_overlap": _overlap(G, direct_G),
        "G_prime_direct_overlap": _overlap(Gp, direct_Gp),
        "G_second_direct_overlap": _overlap(Gpp, direct_Gpp),
        "contrast_trace_zero": True,
        "scalar_removed_before_contraction": True,
    }
    if not all(checks.values()):
        raise AssertionError("scalar-free parity-gap contrast failed direct reconstruction")

    return {
        "G": G,
        "G_prime": Gp,
        "G_second": Gpp,
        "contrast_metadata": parity_gap_contrast_metadata(),
        "checks": checks,
        "scalar_free_matrix_jets": scalar_free,
        "direct_total_matrix_jets": {
            "matrix": direct_M,
            "matrix_prime": direct_Mp,
            "matrix_second": direct_Mpp,
        },
    }


def parity_gap_contrast_json(record: dict) -> dict:
    return {
        "G": ball_record(record["G"]),
        "G_prime": ball_record(record["G_prime"]),
        "G_second": ball_record(record["G_second"]),
        "contrast_metadata": record["contrast_metadata"],
        "checks": record["checks"],
    }
