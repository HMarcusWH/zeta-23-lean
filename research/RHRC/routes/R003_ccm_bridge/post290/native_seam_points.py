"""Source-bound evaluation at the registered symbolic points L=log(n).

At the exact symbolic point floor(exp(log(n)))=n. The entering q=n atom is
exactly zero, by qBasis_aperture_eq_zero (equivalently sourceMatrix_zero at
primeSourceCoordinate=0). We evaluate the n-1 atom sum and retain active Q=n.

The Arb log ball encloses only a SYMBOLIC POINT for this contract. This module
does not assert that the whole ball lies in one physical prime-cutoff cell.
It accepts no arbitrary aperture ball and never nudges L away from the seam.
"""
from __future__ import annotations

REGISTERED_LOG_INTEGERS = (2, 3, 4, 8, 16)
SEAM_BINDINGS = (
    "Zeta23.CCM.qBasis_aperture_eq_zero",
    "Zeta23.CCM.primeSourceCoordinate_log_add",
    "Zeta23.CCM.sourceMatrix_zero",
    "Zeta23.CCM.step123_enteringPrimeSourceMatrix_zero",
    "Zeta23.CCM.step123_qBasis_logSeam_zero",
)


def validate_symbolic_seam(n, K):
    if type(n) is not int or n not in REGISTERED_LOG_INTEGERS or type(K) is not int or K < 0:
        raise ValueError("requires a registered symbolic log integer and a nonnegative integer cutoff")


def seam_receipt(n):
    if n not in REGISTERED_LOG_INTEGERS:
        raise ValueError("unregistered symbolic seam")
    return {"symbolic_aperture": f"log{n}", "active_prime_cutoff": n,
            "evaluated_nonzero_atom_cutoff": n-1, "entering_atom": "EXACT_ZERO",
            "source_theorem_bindings": list(SEAM_BINDINGS),
            "floor_identity": "floor(exp(log(n)))=n for registered positive integer n",
            "whole_arb_ball_fixed_cutoff_claim": False,
            "aperture_nudged": False, "scope": "REGISTERED_SYMBOLIC_POINT_ONLY"}


def direct_at_log_seam(n, K):
    validate_symbolic_seam(n, K)
    import canonical_source_arb as C
    from flint import arb, arb_mat
    L = arb(n).log()
    idx = list(range(-K, K+1))
    alpha = {i: C.alpha_L(i, L) for i in idx}
    beta = {i: C.beta_L(i, L) for i in idx}
    gamma = {i: C.source_eq44_gamma_L(i, L) for i in idx}
    rows = [[arb(0) for _ in idx] for _ in idx]
    for i, left in enumerate(idx):
        for j in range(i, len(idx)):
            right = idx[j]
            value = C.pole_component(left, right, L) - C.direct_arch_component(left, right, L, alpha, beta, gamma) - C.prime_component(left, right, L, n-1)
            rows[i][j] = rows[j][i] = value
    return L, arb_mat(rows)


def signed_at_log_seam(n, K):
    validate_symbolic_seam(n, K)
    import canonical_source_arb as C
    from flint import arb, arb_mat
    L = arb(n).log()
    idx = list(range(-K, K+1))
    alpha = {i: C.alpha_L(i, L) for i in idx}
    beta = {i: C.beta_L(i, L) for i in idx}
    gamma = {i: C.source_eq44_gamma_L(i, L) for i in idx}
    correction = C.c_correction(L)
    channels = {key: [[arb(0) for _ in idx] for _ in idx] for key in ("pole", "arch_signed", "prime_signed", "scalar_shift")}
    for i, left in enumerate(idx):
        for j in range(i, len(idx)):
            right = idx[j]
            shift = 2*correction if i == j else arb(0)
            values = {"pole": C.pole_component(left, right, L),
                      "arch_signed": -C.direct_arch_component(left, right, L, alpha, beta, gamma)-shift,
                      "prime_signed": -C.prime_component(left, right, L, n-1),
                      "scalar_shift": shift}
            for key, value in values.items():
                channels[key][i][j] = channels[key][j][i] = value
    return {key: arb_mat(value) for key, value in channels.items()}
