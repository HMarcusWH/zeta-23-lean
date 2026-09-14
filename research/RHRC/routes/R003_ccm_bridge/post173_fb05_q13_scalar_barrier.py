#!/usr/bin/env python3
"""Dependency-reduced q13/N2/even scalar barrier utilities for post-#173 FB-05 work.

Primary selected successor:
    q=13, predecessor N=2, successor K*=3, parity=even.

In the exact theorem-aligned centered-predecessor / shell coordinates B=[W|c],
the successor restriction is 2x2:

    H = [[a,b],[b,d]],   Delta2 = a*d - b^2.

On H1, a>0, so the selected Schur pivot has the sign of Delta2.  Rigorous
interval classification certifies a and Delta2 directly and never divides by a.

For full post-#150 first-bad ancestry, the only additional nontrivial smaller-
size condition at N=2 is goodness of the odd N=2 predecessor at the same
aperture; sizes 0 and 1 have zero-dimensional parity carriers.

Research/audit tooling only. RH remains OPEN.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from flint import arb, arb_mat

from canonical_source_arb import ball_record, definitely_negative, definitely_positive, von_mangoldt
from canonical_source_numeric import canonical_source_matrix_L, fixed_cell_bounds
from post166_fb05_cell_interval import (
    _arb_matrix_from_sympy,
    arb_unit_interval,
    cell_coordinate_L_arb,
    fixed_q_canonical_source_matrix_arb,
)
from post169_fb05_schur_visibility import one_step_geometry, restricted_step_matrix_float, schur_pivot_float

TARGET_Q_START = 13
TARGET_Q_END = 16
TARGET_N = 2
TARGET_KSTAR = 3
TARGET_PARITY = "even"
PHYSICAL_QS = (13, 14, 15)


@dataclass(frozen=True)
class ScalarGeometry:
    parity: str
    W_norm_sq: int
    c_norm_sq: int


def scalar_geometry(parity: str) -> ScalarGeometry:
    geom = one_step_geometry(TARGET_N, parity)
    if geom.W_exact.cols != 1:
        raise AssertionError(f"expected one-dimensional predecessor for {parity}")
    if geom.step_basis_exact.cols != 2:
        raise AssertionError(f"expected two-dimensional successor for {parity}")
    if any(x != 0 for x in geom.W_exact.T * geom.c_exact):
        raise AssertionError("predecessor/shell orthogonality regression")
    w2 = int((geom.W_exact.T * geom.W_exact)[0, 0])
    c2 = int((geom.c_exact.T * geom.c_exact)[0, 0])
    if w2 <= 0 or c2 <= 0:
        raise AssertionError("nonpositive coordinate norm")
    return ScalarGeometry(parity=parity, W_norm_sq=w2, c_norm_sq=c2)


def _float_step_matrix(L: float, parity: str) -> tuple[np.ndarray, ScalarGeometry]:
    geom = one_step_geometry(TARGET_N, parity)
    M = canonical_source_matrix_L(float(L), TARGET_KSTAR)
    H = restricted_step_matrix_float(M, geom)
    if H.shape != (2, 2):
        raise AssertionError(f"unexpected step restriction shape {H.shape}")
    return H, scalar_geometry(parity)


def scalar_record_float(L: float, parity: str = TARGET_PARITY) -> dict:
    H, norms = _float_step_matrix(float(L), parity)
    a = float(H[0, 0])
    b = float(H[0, 1])
    d = float(H[1, 1])
    delta2 = float(a * d - b * b)
    schur = float(schur_pivot_float(H)["pivot"])
    pivot_from_det = None if a == 0.0 else float(delta2 / a)
    return {
        "L": float(L),
        "physical_Q": int(math.floor(math.exp(float(L)))),
        "parity": parity,
        "a": a,
        "b": b,
        "d": d,
        "delta2": delta2,
        "normalized_a": a / norms.W_norm_sq,
        "normalized_delta2": delta2 / (norms.W_norm_sq * norms.c_norm_sq),
        "raw_schur_pivot": schur,
        "unit_shell_pivot": schur / norms.c_norm_sq,
        "pivot_from_delta_over_a": pivot_from_det,
        "pivot_identity_error": None if pivot_from_det is None else abs(schur - pivot_from_det),
        "H1_float": bool(a > 0.0),
        "W_norm_sq": norms.W_norm_sq,
        "c_norm_sq": norms.c_norm_sq,
    }


def selected_even_and_odd_predecessor_float(L: float) -> dict:
    even = scalar_record_float(L, "even")
    odd = scalar_record_float(L, "odd")
    return {
        "L": float(L),
        "even": even,
        "odd_N2_predecessor_scalar": odd["a"],
        "odd_N2_predecessor_normalized": odd["normalized_a"],
        "odd_N2_predecessor_positive_float": bool(odd["a"] > 0.0),
    }


def _restrict_arb(M: arb_mat, parity: str) -> tuple[arb_mat, ScalarGeometry]:
    geom = one_step_geometry(TARGET_N, parity)
    B = _arb_matrix_from_sympy(geom.step_basis_exact)
    H = B.transpose() * M * B
    if H.nrows() != 2 or H.ncols() != 2:
        raise AssertionError("unexpected Arb step restriction dimension")
    return H, scalar_geometry(parity)


def _scalar_from_H_arb(H: arb_mat, norms: ScalarGeometry) -> dict:
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


def scalar_record_arb_at_L(Q: int, L: arb) -> dict:
    if Q not in (12, 13, 14, 15, 16):
        raise ValueError("q13 barrier helper only supports neighboring Q=12..16")
    M = fixed_q_canonical_source_matrix_arb(L, TARGET_KSTAR, Q)
    He, ne = _restrict_arb(M, "even")
    Ho, no = _restrict_arb(M, "odd")
    even = _scalar_from_H_arb(He, ne)
    odd = _scalar_from_H_arb(Ho, no)
    return {
        "Q": int(Q),
        "L": L,
        "even": even,
        "odd_N2_predecessor": odd["a"],
        "odd_N2_predecessor_normalized": odd["normalized_a"],
    }


def scalar_interval_record_arb(Q: int, lo_num: int, hi_num: int, den: int) -> dict:
    if Q not in PHYSICAL_QS:
        raise ValueError(f"Q must be one of {PHYSICAL_QS}")
    t = arb_unit_interval(lo_num, hi_num, den)
    L = cell_coordinate_L_arb(Q, t)
    rec = scalar_record_arb_at_L(Q, L)
    return {**rec, "t": t, "lo_num": int(lo_num), "hi_num": int(hi_num), "den": int(den)}


def classify_selected_interval(a: arb, delta2: arb) -> str:
    if definitely_negative(a):
        return "EVEN_H1_LOSS_CERTIFIED"
    if not definitely_positive(a):
        return "EVEN_H1_UNRESOLVED"
    if definitely_positive(delta2):
        return "EVEN_STRICT_POSITIVE_CERTIFIED"
    if definitely_negative(delta2):
        return "EVEN_BAD_INTERVAL_CERTIFIED"
    return "EVEN_DETERMINANT_SIGN_UNRESOLVED"


def classify_odd_predecessor(a_odd: arb) -> str:
    if definitely_positive(a_odd):
        return "ODD_N2_PREDECESSOR_POSITIVE_CERTIFIED"
    if definitely_negative(a_odd):
        return "ODD_N2_PREDECESSOR_NEGATIVE_CERTIFIED"
    return "ODD_N2_PREDECESSOR_UNRESOLVED"


def classify_scalar_interval(rec: dict) -> dict:
    selected = classify_selected_interval(rec["even"]["a"], rec["even"]["delta2"])
    ancestry = classify_odd_predecessor(rec["odd_N2_predecessor"])
    if selected == "EVEN_BAD_INTERVAL_CERTIFIED":
        scope = (
            "H3_FIRST_BAD_ALIGNED_INTERVAL_CERTIFIED"
            if ancestry == "ODD_N2_PREDECESSOR_POSITIVE_CERTIFIED"
            else "H2_SELECTED_BAD_SUCCESSOR_CERTIFIED"
        )
    elif selected == "EVEN_STRICT_POSITIVE_CERTIFIED":
        scope = "SELECTED_SUCCESSOR_POSITIVE_CERTIFIED"
    elif selected == "EVEN_H1_LOSS_CERTIFIED":
        scope = "SELECTED_H1_SCOPE_LOST_CERTIFIED"
    else:
        scope = "SCALAR_INTERVAL_UNRESOLVED"
    return {
        "selected_classification": selected,
        "odd_ancestry_classification": ancestry,
        "scope_classification": scope,
    }


def scalar_interval_json_record(rec: dict) -> dict:
    even = rec["even"]
    return {
        "Q": rec["Q"],
        "t_interval": {
            "lo_num": rec["lo_num"], "hi_num": rec["hi_num"], "den": rec["den"],
            "ball": ball_record(rec["t"]),
        },
        "L_ball": ball_record(rec["L"]),
        "even": {
            "a": ball_record(even["a"]), "b": ball_record(even["b"]), "d": ball_record(even["d"]),
            "delta2": ball_record(even["delta2"]),
            "normalized_a": ball_record(even["normalized_a"]),
            "normalized_delta2": ball_record(even["normalized_delta2"]),
        },
        "odd_N2_predecessor": ball_record(rec["odd_N2_predecessor"]),
        "odd_N2_predecessor_normalized": ball_record(rec["odd_N2_predecessor_normalized"]),
        **classify_scalar_interval(rec),
    }


def _overlap(x: arb, y: arb) -> bool:
    return bool((x - y).contains(0))


def seam_overlap_record(k: int) -> dict:
    if k not in (13, 14, 15, 16):
        raise ValueError("seam must be one of 13,14,15,16")
    L = arb(k).log()
    left = scalar_record_arb_at_L(k - 1, L)
    right = scalar_record_arb_at_L(k, L)
    fields = {
        "even_a": (left["even"]["a"], right["even"]["a"]),
        "even_b": (left["even"]["b"], right["even"]["b"]),
        "even_d": (left["even"]["d"], right["even"]["d"]),
        "even_delta2": (left["even"]["delta2"], right["even"]["delta2"]),
        "odd_N2_predecessor": (left["odd_N2_predecessor"], right["odd_N2_predecessor"]),
    }
    overlaps = {name: _overlap(a, b) for name, (a, b) in fields.items()}
    return {
        "k": k, "L": ball_record(L), "left_Q": k - 1, "right_Q": k,
        "overlaps": overlaps, "all_overlap": all(overlaps.values()),
    }


def zero_weight_inertness_record() -> dict:
    vm14 = von_mangoldt(14)
    vm15 = von_mangoldt(15)
    return {
        "von_mangoldt_14_zero": bool(vm14.is_zero()),
        "von_mangoldt_15_zero": bool(vm15.is_zero()),
        "von_mangoldt_14": ball_record(vm14),
        "von_mangoldt_15": ball_record(vm15),
    }


def physical_cell_midpoint(Q: int) -> float:
    lo, hi = fixed_cell_bounds(Q)
    return 0.5 * (lo + hi)
