#!/usr/bin/env python3
"""Rigorous/fail-closed Arb adapter for post-#281 contact-frontier certification.

Certificate decisions stay in Arb arithmetic.  Floating values are display
metadata only and never authorize a sign, residual, gap, or enclosure claim.
Research/audit tooling only.  RH remains OPEN.
"""
from __future__ import annotations

import math
import numpy as np
from flint import arb, arb_mat, ctx
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "closure_batch"))
from interval_codec import DyadicInterval

from post194_fb05_q14_fixed_unit_second_derivative import (
    fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb,
)
from post247_remainder_budget_ratio_scout import (
    _eigs, _rec, _sym, boundary_flat_parity_basis, orthonormalizer, restrict,
)


def _mid_matrix(A: arb_mat) -> np.ndarray:
    return np.array(
        [[float(A[i, j].mid()) for j in range(A.ncols())] for i in range(A.nrows())],
        dtype=float,
    )


def _outward_float_bounds(lo: arb, hi: arb) -> tuple[float | None, float | None]:
    """Display-only outward float endpoints. Never use for certificate logic."""
    lf, uf = float(lo), float(hi)
    if not (math.isfinite(lf) and math.isfinite(uf)):
        return None, None
    return math.nextafter(lf, -math.inf), math.nextafter(uf, math.inf)


def _ball_record_full(x: arb) -> dict:
    rec = _rec(x)
    lo, hi = x.lower(), x.upper()
    flo, fhi = _outward_float_bounds(lo, hi)
    rec.update({
        "dyadic_interval": DyadicInterval.from_arb(x).to_json(),
        "lower": flo,
        "upper": fhi,
        "lower_exact": lo.str(40, radius=False),
        "upper_exact": hi.str(40, radius=False),
        "mid_exact": x.mid().str(40, radius=False),
        "rad_exact": x.rad().str(20, radius=False),
        "certified_positive": bool(x > 0),
        "certified_negative": bool(x < 0),
    })
    return rec


def _bounds_record(lo: arb, hi: arb) -> dict:
    # Reconstruct one enclosing Arb ball, then derive *all* serialized endpoints
    # from that same object.  Mid/radius arithmetic can widen the directed
    # input endpoints by a few ulps; using the pre-reconstruction lo/hi for
    # display metadata would then make the display interval cut inside the
    # exact dyadic certificate.
    exact_ball = arb((lo + hi) / 2, (hi - lo) / 2)
    enc_lo, enc_hi = exact_ball.lower(), exact_ball.upper()
    flo, fhi = _outward_float_bounds(enc_lo, enc_hi)
    return {
        "dyadic_interval": DyadicInterval.from_arb(exact_ball).to_json(),
        "lower": flo,
        "upper": fhi,
        "lower_exact": enc_lo.str(40, radius=False),
        "upper_exact": enc_hi.str(40, radius=False),
        "certified_positive": bool(enc_lo > 0),
        "certified_negative": bool(enc_hi < 0),
        "contains_zero": not (bool(enc_lo > 0) or bool(enc_hi < 0)),
    }


def _arb_col(v: np.ndarray) -> arb_mat:
    return arb_mat([[arb(repr(float(x)))] for x in np.asarray(v, dtype=float)])


def _norm_sq(V: arb_mat) -> arb:
    return (V.transpose() * V)[0, 0]


def _quad_quotient(A: arb_mat, V: arb_mat) -> arb:
    den = _norm_sq(V)
    if not bool(den > 0):
        raise ArithmeticError("vector norm is not certified positive")
    return (V.transpose() * A * V)[0, 0] / den


def _frobenius_upper_arb(A: arb_mat) -> arb:
    s = arb(0)
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            u = abs(A[i, j]).upper()
            s += u * u
    return s.sqrt().upper()


def _residual_upper_arb(H: arb_mat, V: arb_mat, theta: arb) -> arb:
    R = H * V - theta * V
    s = arb(0)
    for i in range(R.nrows()):
        u = abs(R[i, 0]).upper()
        s += u * u
    return s.sqrt().upper()


def restricted_jets(L: arb, K: int, Q: int, parity: str):
    M, Mp, Mpp = fixed_unit_fixed_q_canonical_source_matrix_with_second_derivative_arb(
        L, K, Q
    )
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
    rec = {"precision_bits": int(prec), "dimension": H.nrows()}
    try:
        eigs = _eigs(H)
    except ValueError as exc:
        rec["simple_status"] = "EIGENSOLVER_UNRESOLVED"
        rec["eigensolver_error"] = str(exc)
        return rec

    rec.update({
        "lambda_min": _ball_record_full(eigs[0]),
        "lambda_2": _ball_record_full(eigs[1]) if len(eigs) > 1 else None,
    })

    if H.nrows() == 1:
        V = _arb_col(np.ones(1))
        rec["simple_status"] = "CERTIFIED_ONE_DIMENSIONAL"
        rec["vector_norm_sq"] = _ball_record_full(_norm_sq(V))
        rec["j1"] = _ball_record_full(_quad_quotient(Hp, V))
        rec["fixed_second"] = _ball_record_full(_quad_quotient(Hpp, V))
        rec["vector_error_status"] = "EXACT_ONE_DIMENSIONAL_DIRECTION"
        return rec

    gap = eigs[1].lower() - eigs[0].upper()
    rec["ground_gap"] = _bounds_record(gap, gap)
    if not bool(gap > 0):
        rec["simple_status"] = "GROUND_CLUSTER_UNRESOLVED"
        return rec

    Hmid = _mid_matrix(H)
    _vals, vecs = np.linalg.eigh((Hmid + Hmid.T) / 2)
    V = _arb_col(vecs[:, 0])
    norm_sq = _norm_sq(V)
    rec["vector_norm_sq"] = _ball_record_full(norm_sq)
    if not bool(norm_sq > 0):
        rec["simple_status"] = "EIGENVECTOR_NORM_UNRESOLVED"
        return rec

    theta = _quad_quotient(H, V)
    residual = _residual_upper_arb(H, V, theta)
    norm_lower = norm_sq.lower().sqrt()
    if not bool(norm_lower > 0):
        rec["simple_status"] = "EIGENVECTOR_NORM_UNRESOLVED"
        return rec
    residual_rel = residual / norm_lower
    sep = eigs[1].lower() - theta.upper()

    rec["rayleigh"] = _ball_record_full(theta)
    rec["residual_norm_upper_exact"] = residual.str(30, radius=False)
    rec["relative_residual_upper_exact"] = residual_rel.str(30, radius=False)
    rec["separation_from_second"] = _bounds_record(sep, sep)
    if not bool(sep > 0):
        rec["simple_status"] = "EIGENVECTOR_ENCLOSURE_UNRESOLVED"
        return rec

    angle = residual_rel / sep
    if bool(angle > 1):
        angle = arb(1)
    rec["angle_sin_upper_exact"] = angle.upper().str(30, radius=False)
    rec["simple_status"] = "SIMPLE_GROUND_RESOLVED"

    for name, A in (("j1", Hp), ("fixed_second", Hpp)):
        q = _quad_quotient(A, V)
        err = arb(3) * _frobenius_upper_arb(A) * angle.upper()
        lo = q.lower() - err.upper()
        hi = q.upper() + err.upper()
        qrec = _bounds_record(lo, hi)
        qrec.update({
            "midpoint_rayleigh": _ball_record_full(q),
            "eigenvector_error_budget_exact": err.upper().str(30, radius=False),
        })
        rec[name] = qrec
    return rec


def certify_point(L_value, Q: int, K: int, prec: int) -> dict:
    ctx.prec = int(prec)
    if isinstance(L_value, arb):
        L = L_value
        L_float = float(L.mid())
        L_exact = L.mid().str(40, radius=False)
    else:
        L = arb(repr(float(L_value)))
        L_float = float(L_value)
        L_exact = L.str(40, radius=False)

    even = certify_simple_ground_jet(L, K, Q, "even", prec)
    odd = certify_simple_ground_jet(L, K, Q, "odd", prec)
    if "lambda_min" not in even or "lambda_min" not in odd:
        regime = "PARITY_UNRESOLVED"
    else:
        le, lo = even["lambda_min"], odd["lambda_min"]
        even_strict = (
            le["upper"] is not None and lo["lower"] is not None
            and le["upper"] < lo["lower"]
        )
        odd_strict = (
            lo["upper"] is not None and le["lower"] is not None
            and lo["upper"] < le["lower"]
        )
        regime = (
            "EVEN_STRICT" if even_strict
            else "ODD_STRICT" if odd_strict
            else "PARITY_UNRESOLVED"
        )
    return {
        "Q": int(Q),
        "K": int(K),
        "L_float": L_float,
        "L_exact": L_exact,
        "precision_bits": int(prec),
        "even": even,
        "odd": odd,
        "spectral_regime": regime,
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "terminal_claim": "RH_OPEN",
    }


def global_bottom_bounds(record: dict):
    """Display-only outward bounds for min(even,odd)."""
    try:
        e = record["even"]["lambda_min"]
        o = record["odd"]["lambda_min"]
        if None in (e["lower"], e["upper"], o["lower"], o["upper"]):
            return None
        return {
            "lower": min(e["lower"], o["lower"]),
            "upper": min(e["upper"], o["upper"]),
        }
    except (KeyError, TypeError, ValueError):
        return None


def global_bottom_sign(record: dict) -> str:
    """Certificate sign from Arb-derived booleans, never rounded float endpoints."""
    try:
        e = record["even"]["lambda_min"]
        o = record["odd"]["lambda_min"]
    except (KeyError, TypeError):
        return "UNRESOLVED"
    if e.get("certified_positive") and o.get("certified_positive"):
        return "POSITIVE"
    if e.get("certified_negative") or o.get("certified_negative"):
        return "NEGATIVE"
    return "UNRESOLVED"
