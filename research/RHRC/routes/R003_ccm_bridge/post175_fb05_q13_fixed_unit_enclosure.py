#!/usr/bin/env python3
"""Fixed-unit Arb enclosure utilities for the post-#175 FB-05 q13 benchmark.

This module ports the exact fixed-unit production identities already theoremized
in ``CanonicalApertureAnalyticPrimitives.lean`` into the rigorous Arb research
backend.  It does not replace ``canonical_source_arb.py``: that direct [0,L]
evaluator remains the independent production baseline.

Only the archimedean representation changes.  Pole terms, von-Mangoldt prime
terms, fixed-Q seam semantics, theorem-aligned [W|c] geometry, and the q13
selected scalar observables are unchanged.

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
    ball_record,
    direct_arch_component,
    pole_component,
    prime_component,
    w_correction,
)
from post166_fb05_cell_interval import (
    _arb_matrix_from_sympy,
    arb_unit_interval,
    cell_coordinate_L_arb,
)
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import (
    PHYSICAL_QS,
    TARGET_KSTAR,
    TARGET_N,
    scalar_geometry,
)

SUPPORTED_QS = (12, 13, 14, 15, 16)


def _unit_integral_real(func) -> arb:
    """Rigorous real integral on the fixed interval [0,1]."""
    return _integral_real(func, arb(1))


def fixed_unit_alpha_L(n: int, L: arb) -> arb:
    """Exact fixed-unit production alpha primitive.

    Lean identity:
      alphaL n L = 2*n * int_0^1 sinc(2*pi*n*t) R(L*t) dt.
    """
    two_pi_n = acb(2 * arb.pi() * n)
    Lc = acb(L)
    return arb(2 * n) * _unit_integral_real(
        lambda t: (two_pi_n * t).sinc() * _regularized_arch_scale(Lc * t)
    )


def fixed_unit_beta_L(n: int, L: arb) -> arb:
    """Exact fixed-unit production beta primitive."""
    two_pi_n = acb(2 * arb.pi() * n)
    Lc = acb(L)
    return _unit_integral_real(
        lambda t: (two_pi_n * t).cos() * _regularized_arch_scale(Lc * t)
    )


def fixed_unit_source_eq44_gamma_L(n: int, L: arb) -> arb:
    """Exact fixed-unit direct equation-(4.4) gamma primitive + w(L)."""
    two_pi_n = acb(2 * arb.pi() * n)
    Lc = acb(L)

    def integrand(t: acb) -> acb:
        Lt = Lc * t
        coeff = (
            two_pi_n * _cos_slope(two_pi_n * t)
            + (Lc / 2) * _exp_slope(-Lt / 2)
        )
        return coeff * _regularized_arch_scale(Lt)

    return _unit_integral_real(integrand) + w_correction(L)


def fixed_unit_primitive_caches(L: arb, N: int) -> dict:
    if N < 0:
        raise ValueError("require N>=0")
    idx = list(range(-N, N + 1))
    return {
        "alpha": {n: fixed_unit_alpha_L(n, L) for n in idx},
        "beta": {n: fixed_unit_beta_L(n, L) for n in idx},
        "gamma": {n: fixed_unit_source_eq44_gamma_L(n, L) for n in idx},
    }


def fixed_unit_fixed_q_canonical_source_matrix_arb(L: arb, N: int, Q: int) -> arb_mat:
    """Fixed-Q canonical source using only the fixed-unit arch representation."""
    if N < 0 or Q < 1:
        raise ValueError("require N>=0 and Q>=1")
    idx = list(range(-N, N + 1))
    caches = fixed_unit_primitive_caches(L, N)
    rows = [[arb(0) for _ in idx] for _ in idx]
    for r, n in enumerate(idx):
        for c in range(r, len(idx)):
            m = idx[c]
            value = (
                pole_component(n, m, L)
                - direct_arch_component(
                    n, m, L,
                    caches["alpha"], caches["beta"], caches["gamma"],
                )
                - prime_component(n, m, L, Q)
            )
            rows[r][c] = value
            rows[c][r] = value
    return arb_mat(rows)


def _restrict_arb(M: arb_mat, parity: str) -> tuple[arb_mat, object]:
    geom = one_step_geometry(TARGET_N, parity)
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * M * B
    if H.nrows() != 2 or H.ncols() != 2:
        raise AssertionError("unexpected fixed-unit Arb step restriction dimension")
    return H, scalar_geometry(parity)


def _scalar_from_H_arb(H: arb_mat, norms) -> dict:
    a = H[0, 0]
    b = H[0, 1]
    d = H[1, 1]
    delta2 = a * d - b * b
    return {
        "a": a,
        "b": b,
        "d": d,
        "delta2": delta2,
        "normalized_a": a / norms.W_norm_sq,
        "normalized_delta2": delta2 / (norms.W_norm_sq * norms.c_norm_sq),
    }


def fixed_unit_scalar_record_arb_at_L(Q: int, L: arb) -> dict:
    if Q not in SUPPORTED_QS:
        raise ValueError(f"fixed-unit q13 helper supports Q in {SUPPORTED_QS}")
    M = fixed_unit_fixed_q_canonical_source_matrix_arb(L, TARGET_KSTAR, Q)
    He, ne = _restrict_arb(M, "even")
    Ho, no = _restrict_arb(M, "odd")
    even = _scalar_from_H_arb(He, ne)
    odd = _scalar_from_H_arb(Ho, no)
    return {
        "Q": int(Q),
        "L": L,
        "matrix": M,
        "even_H": He,
        "odd_H": Ho,
        "even": even,
        "odd_N2_predecessor": odd["a"],
        "odd_N2_predecessor_normalized": odd["normalized_a"],
    }


def fixed_unit_scalar_interval_record_arb(Q: int, lo_num: int, hi_num: int, den: int) -> dict:
    if Q not in PHYSICAL_QS:
        raise ValueError(f"Q must be one of {PHYSICAL_QS}")
    t = arb_unit_interval(lo_num, hi_num, den)
    L = cell_coordinate_L_arb(Q, t)
    rec = fixed_unit_scalar_record_arb_at_L(Q, L)
    return {
        **rec,
        "t": t,
        "lo_num": int(lo_num),
        "hi_num": int(hi_num),
        "den": int(den),
    }


def arb_width(x: arb) -> arb:
    return x.upper() - x.lower()


def overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def matrix_overlap(A: arb_mat, B: arb_mat) -> bool:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        return False
    return all(overlap(A[r, c], B[r, c]) for r in range(A.nrows()) for c in range(A.ncols()))


def fixed_unit_seam_overlap_record(k: int) -> dict:
    if k not in (13, 14, 15, 16):
        raise ValueError("seam must be one of 13,14,15,16")
    L = arb(k).log()
    left = fixed_unit_scalar_record_arb_at_L(k - 1, L)
    right = fixed_unit_scalar_record_arb_at_L(k, L)
    fields = {
        "even_a": (left["even"]["a"], right["even"]["a"]),
        "even_b": (left["even"]["b"], right["even"]["b"]),
        "even_d": (left["even"]["d"], right["even"]["d"]),
        "even_delta2": (left["even"]["delta2"], right["even"]["delta2"]),
        "odd_N2_predecessor": (left["odd_N2_predecessor"], right["odd_N2_predecessor"]),
    }
    overlaps = {name: overlap(a, b) for name, (a, b) in fields.items()}
    return {
        "k": k,
        "L": ball_record(L),
        "left_Q": k - 1,
        "right_Q": k,
        "overlaps": overlaps,
        "all_overlap": all(overlaps.values()),
    }
