#!/usr/bin/env python3
"""Reusable Arb adapter for post-#281 contact-frontier certification.

The adapter consumes the previously validated fixed-Q analytic derivative
backends and exact integer boundary-flat parity bases.  It keeps every status
fail-closed.  Approximate vectors are never promoted to exact eigenvectors.

Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

import math
import numpy as np
from flint import arb, arb_mat, ctx

from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb,
)
from post247_remainder_budget_ratio_scout import (
    _eigs, _rec, _sym, boundary_flat_parity_basis, orthonormalizer, restrict,
)


def _mid_matrix(A: arb_mat) -> np.ndarray:
    return np.array([[float(A[i,j].mid()) for j in range(A.ncols())] for i in range(A.nrows())], dtype=float)


def _arb_col(v: np.ndarray) -> arb_mat:
    return arb_mat([[arb(repr(float(x)))] for x in np.asarray(v, dtype=float)])


def _quad(A: arb_mat, v: np.ndarray) -> arb:
    V = _arb_col(v)
    return (V.transpose() * A * V)[0,0]


def _frobenius_upper(A: arb_mat) -> float:
    s = 0.0
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            s += float(abs(A[i,j]).upper()) ** 2
    return math.sqrt(s)


def _residual_upper(H: arb_mat, v: np.ndarray, theta: arb) -> float:
    V = _arb_col(v)
    R = H * V - theta * V
    return math.sqrt(sum(float(abs(R[i,0]).upper())**2 for i in range(R.nrows())))


def restricted_jets(L: arb, K: int, Q: int, parity: str):
    M, Mp, Mpp = fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(L, K, Q)
    V = boundary_flat_parity_basis(K, parity)
    Linv = orthonormalizer(V)
    return (
        _sym(restrict(M, V, Linv)),
        _sym(restrict(Mp, V, Linv)),
        _sym(restrict(Mpp, V, Linv)),
    )


def certify_simple_ground_jet(L: arb, K: int, Q: int, parity: str, prec: int) -> dict:
    ctx.prec = int(prec)
    H, Hp, Hpp = restricted_jets(L, K, Q, parity)
    eigs = _eigs(H)
    rec = {
        "precision_bits": int(prec),
        "lambda_min": _rec(eigs[0]),
        "lambda_2": _rec(eigs[1]) if len(eigs)>1 else None,
        "dimension": H.nrows(),
    }
    if H.nrows() == 1:
        v = np.ones(1)
        rec["simple_status"] = "CERTIFIED_ONE_DIMENSIONAL"
        rec["j1"] = _rec(_quad(Hp,v))
        rec["fixed_second"] = _rec(_quad(Hpp,v))
        rec["vector_error_status"] = "EXACT_ONE_DIMENSIONAL_DIRECTION"
        return rec

    gap_lower = float(eigs[1].lower() - eigs[0].upper())
    rec["ground_gap_lower"] = gap_lower
    if not gap_lower > 0:
        rec["simple_status"] = "GROUND_CLUSTER_UNRESOLVED"
        return rec

    Hmid = _mid_matrix(H)
    vals, vecs = np.linalg.eigh((Hmid+Hmid.T)/2)
    v = vecs[:,0]
    v = v / np.linalg.norm(v)
    theta = _quad(H,v)
    residual = _residual_upper(H,v,theta)
    sep = float(eigs[1].lower() - theta.upper())
    rec["rayleigh"] = _rec(theta)
    rec["residual_norm_upper"] = residual
    rec["separation_from_second_lower"] = sep
    if not sep > 0:
        rec["simple_status"] = "EIGENVECTOR_ENCLOSURE_UNRESOLVED"
        return rec

    angle = min(1.0, residual/sep)
    rec["angle_sin_upper"] = angle
    rec["simple_status"] = "SIMPLE_GROUND_RESOLVED"
    for name,A in (("j1",Hp),("fixed_second",Hpp)):
        q = _quad(A,v)
        err = 3.0 * _frobenius_upper(A) * angle
        rec[name] = {
            "lower": float(q.lower()) - err,
            "upper": float(q.upper()) + err,
            "midpoint_rayleigh": _rec(q),
            "eigenvector_error_budget": err,
            "certified_positive": float(q.lower()) - err > 0,
            "certified_negative": float(q.upper()) + err < 0,
            "contains_zero": not (float(q.lower()) - err > 0 or float(q.upper()) + err < 0),
        }
    return rec


def certify_point(L_value: float, Q: int, K: int, prec: int) -> dict:
    L = arb(repr(float(L_value)))
    even = certify_simple_ground_jet(L,K,Q,"even",prec)
    odd = certify_simple_ground_jet(L,K,Q,"odd",prec)
    le = even["lambda_min"]; lo = odd["lambda_min"]
    even_strict = le["upper"] < lo["lower"]
    odd_strict = lo["upper"] < le["lower"]
    return {
        "Q":int(Q),"K":int(K),"L_float":float(L_value),"precision_bits":int(prec),
        "even":even,"odd":odd,
        "spectral_regime":"EVEN_STRICT" if even_strict else "ODD_STRICT" if odd_strict else "PARITY_UNRESOLVED",
        "claim_cap":"EXPERIMENTAL_SIGNAL_ONLY",
        "terminal_claim":"RH_OPEN",
    }
