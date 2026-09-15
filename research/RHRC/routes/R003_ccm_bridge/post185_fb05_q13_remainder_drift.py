#!/usr/bin/env python3
"""Post-#185 q13/Q14 remainder-drift decomposition utilities.

This module reuses the complete physical-L canonical derivative backend validated
by #178 and the exact-center / correlation-preserving Schur graph validated by
#180. It does not differentiate the canonical source again.

In the existing orthogonal research coordinates B=[W|c], with

    H = [[a,b],[b,d]],  x=b/a,

and exact coordinate norms w2=||W||^2, c2=||c||^2, the scalar source split
M(L)=-log(L)I+R(L) gives

    a_R' = a' + w2/L,
    b_R' = b',
    d_R' = d' + c2/L.

Therefore

    E = c2 + x^2*w2,
    P_L' = -E/L + R_L',
    R_L' = d_R' - 2*x*b_R' + x^2*a_R'.

The direct remainder-coordinate graph is cross-checked against the residual
graph R_L'=P_L'+E/L. Research/audit tooling only; no output here is Lean
theorem authority. RH remains OPEN.
"""
from __future__ import annotations

from flint import arb

from canonical_source_arb import definitely_positive
from post173_fb05_q13_scalar_barrier import scalar_geometry
from post179_fb05_q13_correlation_preserving_derivative import (
    interval_record_from_box,
    overlap,
    point_record_from_box,
    sign_class,
)


def ratio_vs_one_class(ratio_gap: arb) -> str:
    """Classify 1-ratio without nonrigorous midpoint comparisons."""
    sign = sign_class(ratio_gap)
    if sign == "POSITIVE_CERTIFIED":
        return "LT_ONE_CERTIFIED"
    if sign == "NEGATIVE_CERTIFIED":
        return "GT_ONE_CERTIFIED"
    return "UNRESOLVED"


def remainder_drift_from_even(even: dict, L: arb) -> dict:
    """Return the H1-guarded physical-L universal/remainder Schur split."""
    a = even["a"]
    if not definitely_positive(a):
        return {
            "h1_certified": False,
            "scope": "OUT_OF_CERTIFIED_H1_SCOPE",
        }

    norms = scalar_geometry("even")
    w2 = arb(norms.W_norm_sq)
    c2 = arb(norms.c_norm_sq)
    if not definitely_positive(L):
        raise AssertionError("remainder-drift evaluation requires L>0")
    if norms.W_norm_sq <= 0 or norms.c_norm_sq <= 0:
        raise AssertionError("nonpositive coordinate norm regression")

    b = even["b"]
    ap = even["a_prime"]
    bp = even["b_prime"]
    dp = even["d_prime"]
    x = b / a

    envelope = c2 + x * x * w2
    if not definitely_positive(envelope):
        raise AssertionError("envelope norm square failed positivity")

    a_remainder_prime = ap + w2 / L
    b_remainder_prime = bp
    d_remainder_prime = dp + c2 / L

    full_pivot_prime = dp - 2 * bp * x + ap * x * x
    universal_log_drift = -envelope / L
    remainder_direct = (
        d_remainder_prime
        - 2 * b_remainder_prime * x
        + a_remainder_prime * x * x
    )
    remainder_residual = full_pivot_prime - universal_log_drift
    reconstructed_full = universal_log_drift + remainder_direct

    domination_margin = envelope / L - remainder_direct
    normalized_ratio = L * remainder_direct / envelope
    ratio_gap = arb(1) - normalized_ratio
    scaled_margin = L * domination_margin / envelope

    return {
        "h1_certified": True,
        "scope": "CERTIFIED_H1_SCOPE",
        "W_norm_sq": w2,
        "c_norm_sq": c2,
        "x": x,
        "envelope_norm_sq": envelope,
        "a_remainder_prime": a_remainder_prime,
        "b_remainder_prime": b_remainder_prime,
        "d_remainder_prime": d_remainder_prime,
        "universal_log_drift_L": universal_log_drift,
        "remainder_envelope_derivative_L": remainder_direct,
        "remainder_envelope_derivative_residual_L": remainder_residual,
        "full_pivot_derivative_L": full_pivot_prime,
        "reconstructed_full_pivot_derivative_L": reconstructed_full,
        "domination_margin_L": domination_margin,
        "normalized_ratio": normalized_ratio,
        "ratio_gap_to_one": ratio_gap,
        "scaled_margin": scaled_margin,
        "margin_sign": sign_class(domination_margin),
        "ratio_vs_one": ratio_vs_one_class(ratio_gap),
        "remainder_direct_residual_overlap": overlap(remainder_direct, remainder_residual),
        "full_decomposition_overlap": overlap(full_pivot_prime, reconstructed_full),
        "ratio_margin_identity_overlap": overlap(ratio_gap, scaled_margin),
    }


def point_remainder_drift_record(box: dict) -> dict:
    base = point_record_from_box(box)
    dec = remainder_drift_from_even(base["record"]["even"], base["L"])
    if dec["h1_certified"] and base["schur"]["h1_certified"]:
        dec["existing_schur_pivot_derivative_overlap"] = overlap(
            dec["full_pivot_derivative_L"],
            base["schur"]["pivot_prime_directional"],
        )
    else:
        dec["existing_schur_pivot_derivative_overlap"] = False
    return {"base": base, "decomposition": dec}


def interval_remainder_drift_record(box: dict) -> dict:
    base = interval_record_from_box(box)
    dec = remainder_drift_from_even(base["record"]["even"], base["L"])
    if dec["h1_certified"] and base["schur"]["h1_certified"]:
        dec["existing_schur_pivot_derivative_overlap"] = overlap(
            dec["full_pivot_derivative_L"],
            base["schur"]["pivot_prime_directional"],
        )
    else:
        dec["existing_schur_pivot_derivative_overlap"] = False
    return {"base": base, "decomposition": dec}
