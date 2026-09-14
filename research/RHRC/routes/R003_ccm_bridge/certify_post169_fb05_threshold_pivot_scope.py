#!/usr/bin/env python3
"""Rigorous pointwise Arb replay for post-#169 Schur visibility research.

This certifies finite theorem-aligned [W|c] Schur data and finite-difference
enclosures only. It does not promote those finite differences to derivative
theorems or claim whole-cell positivity, FB-05 closure, or RH.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import sympy as sp
from flint import arb, arb_mat

from canonical_source_arb import (
    ball_record,
    canonical_source_matrix,
    definitely_negative,
    definitely_nonzero,
    definitely_positive,
    set_precision,
)
from certify_post150_selected_residual_scope import positive_definite_certificate
from post150_selected_residual import centered_predecessor_basis, exact_shell_generator
from post166_fb05_cell_interval import _arb_matrix_from_sympy, fixed_q_canonical_source_matrix_arb
from post167_fb05_threshold_jet import canonical_entering_atom_arb, centered_moment_row, von_mangoldt_weight_arb

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post169_fb05_threshold_pivot_v1.json"


def _scalar(M: arb_mat) -> arb:
    if M.nrows() != 1 or M.ncols() != 1:
        raise ValueError("expected 1x1 matrix")
    return M[0, 0]


def _submatrix(H: arb_mat, rows: range, cols: range) -> arb_mat:
    return arb_mat([[H[r, c] for c in cols] for r in rows])


def _step_basis(N: int, parity: str):
    W = centered_predecessor_basis(N, parity)
    c = exact_shell_generator(N, parity)
    B = sp.Matrix.hstack(W, c)
    c2 = int((c.T * c)[0, 0])
    return W, c, B, c2


def _restricted(M: arb_mat, B) -> arb_mat:
    Bb = _arb_matrix_from_sympy(B)
    return Bb.transpose() * M * Bb


def _schur_record(H: arb_mat) -> dict:
    n = H.nrows()
    if n < 1 or H.ncols() != n:
        raise ValueError("expected nonempty square one-step matrix")
    if n == 1:
        return {
            "A": arb_mat(0, 0), "b": arb_mat(0, 1), "x": arb_mat(0, 1),
            "pivot": H[0, 0], "predecessor_pd": positive_definite_certificate(arb_mat(0, 0))
        }
    A = _submatrix(H, range(n - 1), range(n - 1))
    b = _submatrix(H, range(n - 1), range(n - 1, n))
    pd = positive_definite_certificate(A)
    if not pd["certified"]:
        return {"A": A, "b": b, "x": None, "pivot": None, "predecessor_pd": pd}
    x = A.solve(b)
    pivot = H[n - 1, n - 1] - _scalar(b.transpose() * x)
    return {"A": A, "b": b, "x": x, "pivot": pivot, "predecessor_pd": pd}


def _visibility(H: arb_mat, v: list[int]) -> dict:
    rec = _schur_record(H)
    if rec["pivot"] is None:
        return {"available": False, "predecessor_pd": rec["predecessor_pd"]}
    n = H.nrows()
    alpha = arb(int(v[-1]))
    if n == 1:
        rho, gamma = alpha, arb(0)
    else:
        a = arb_mat([[int(x)] for x in v[:-1]])
        z = rec["A"].solve(a)
        rho = alpha - _scalar(a.transpose() * rec["x"])
        gamma = _scalar(a.transpose() * z)
    return {
        "available": True,
        "rho": rho,
        "gamma": gamma,
        "rho_nonzero_certified": definitely_nonzero(rho),
        "predecessor_pd": rec["predecessor_pd"]
    }


def _entrywise_overlap(A: arb_mat, B: arb_mat) -> bool:
    return A.nrows() == B.nrows() and A.ncols() == B.ncols() and all(
        (A[r, c] - B[r, c]).contains(0)
        for r in range(A.nrows()) for c in range(A.ncols())
    )


def _sign_class(x: arb | None) -> str:
    if x is None:
        return "UNRESOLVED"
    if definitely_positive(x):
        return "POSITIVE_CERTIFIED"
    if definitely_negative(x):
        return "NEGATIVE_CERTIFIED"
    return "UNRESOLVED"


def _kappa(q: int, parity: str) -> tuple[int, arb]:
    weight = von_mangoldt_weight_arb(q)
    pi = arb.pi()
    if parity == "odd":
        return 7, weight * 2 * (2 * pi) ** 6 / math.factorial(7)
    if parity == "even":
        return 9, -weight * 2 * (2 * pi) ** 8 / math.factorial(9)
    raise ValueError("parity must be odd/even")


def _moment_vector(N: int, parity: str, B) -> list[int]:
    order = 3 if parity == "odd" else 4
    row = centered_moment_row(N + 1, B, order)
    return [int(row[0, j]) for j in range(row.cols)]


def _rank_one_formula_effect(Hbg: arb_mat, tau: arb, v: list[int]) -> arb | None:
    vis = _visibility(Hbg, v)
    if not vis["available"]:
        return None
    return tau * vis["rho"] ** 2 / (1 + tau * vis["gamma"])


def _background_schur_at_signed_offset(q: int, N: int, parity: str, sign: int, exponent: int) -> dict:
    den = 1 << exponent
    omega = arb(sign) / den
    L = arb(q).log() / (1 - omega)
    _W, _c, B, c2 = _step_basis(N, parity)
    physical_Q = q - 1 if sign < 0 else q
    full = canonical_source_matrix(L, N + 1, physical_Q)
    if sign > 0:
        atom = canonical_entering_atom_arb(q, N + 1, omega)
        bg = full - atom
    else:
        bg = full
    rec = _schur_record(_restricted(bg, B))
    return {
        "omega": omega, "L": L, "physical_Q": physical_Q,
        "pivot": rec["pivot"], "unit_pivot": None if rec["pivot"] is None else rec["pivot"] / c2,
        "H1": bool(rec["predecessor_pd"]["certified"])
    }


def _finite_difference(q: int, N: int, parity: str, exponent: int) -> dict:
    minus = _background_schur_at_signed_offset(q, N, parity, -1, exponent)
    plus = _background_schur_at_signed_offset(q, N, parity, 1, exponent)
    h = arb(1) / (1 << exponent)
    beta = None
    if minus["unit_pivot"] is not None and plus["unit_pivot"] is not None:
        beta = (plus["unit_pivot"] - minus["unit_pivot"]) / (2 * h)
    return {
        "exponent": exponent,
        "h": ball_record(h),
        "H1_minus": minus["H1"], "H1_plus": plus["H1"],
        "unit_background_central_difference": None if beta is None else ball_record(beta),
        "sign": _sign_class(beta),
        "claim_cap": "RIGOROUS_FINITE_DIFFERENCE_ENCLOSURE_ONLY"
    }


def _point(q: int, N: int, parity: str, exponent: int) -> dict:
    den = 1 << exponent
    omega = arb(1) / den
    L = arb(q).log() / (1 - omega)
    _W, _c, B, c2 = _step_basis(N, parity)
    full = canonical_source_matrix(L, N + 1, q)
    atom = canonical_entering_atom_arb(q, N + 1, omega)
    background = full - atom
    reconstruction = _entrywise_overlap(full, background + atom)
    Hfull, Hbg = _restricted(full, B), _restricted(background, B)
    full_rec, bg_rec = _schur_record(Hfull), _schur_record(Hbg)
    v = _moment_vector(N, parity, B)
    order, kappa = _kappa(q, parity)
    tau = kappa * omega ** order
    model_effect = _rank_one_formula_effect(Hbg, tau, v) if bg_rec["pivot"] is not None else None
    exact_effect = full_rec["pivot"] - bg_rec["pivot"] if full_rec["pivot"] is not None and bg_rec["pivot"] is not None else None
    residual = exact_effect - model_effect if exact_effect is not None and model_effect is not None else None
    return {
        "exponent": exponent,
        "omega": ball_record(omega), "L": ball_record(L),
        "full_equals_background_plus_q_atom": reconstruction,
        "H1_background_certified": bool(bg_rec["predecessor_pd"]["certified"]),
        "H1_full_certified": bool(full_rec["predecessor_pd"]["certified"]),
        "background_unit_pivot": None if bg_rec["pivot"] is None else ball_record(bg_rec["pivot"] / c2),
        "full_unit_pivot": None if full_rec["pivot"] is None else ball_record(full_rec["pivot"] / c2),
        "exact_q_effect": None if exact_effect is None else ball_record(exact_effect),
        "exact_q_effect_sign": _sign_class(exact_effect),
        "rank_one_formula_effect": None if model_effect is None else ball_record(model_effect),
        "rank_one_formula_effect_sign": _sign_class(model_effect),
        "exact_minus_rank_one": None if residual is None else ball_record(residual),
        "claim_cap": "RIGOROUS_FINITE_POINT_AUDIT_ONLY"
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST169_FB05_SCHUR_VISIBILITY_CERTIFICATE.json"))
    ap.add_argument("--precision-bits", type=int, default=None)
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    target = fixture["target"]
    q, N, parity = int(target["q"]), int(target["predecessor_N"]), target["selected_parity"]
    precision = int(args.precision_bits or fixture.get("arb_precision_bits", 256))
    set_precision(precision)

    _W, _c, B, c2 = _step_basis(N, parity)
    L0 = arb(q).log()
    background0 = fixed_q_canonical_source_matrix_arb(L0, N + 1, q - 1)
    H0 = _restricted(background0, B)
    schur0 = _schur_record(H0)
    v = _moment_vector(N, parity, B)
    visibility = _visibility(H0, v)
    threshold = {
        "L": ball_record(L0),
        "H1_predecessor_positive_certified": bool(schur0["predecessor_pd"]["certified"]),
        "raw_pivot": None if schur0["pivot"] is None else ball_record(schur0["pivot"]),
        "unit_shell_pivot": None if schur0["pivot"] is None else ball_record(schur0["pivot"] / c2),
        "shell_norm_sq": c2,
        "moment_vector_in_step_basis": v,
        "visibility": {
            "available": visibility["available"],
            "rho": None if not visibility["available"] else ball_record(visibility["rho"]),
            "rho_nonzero_certified": False if not visibility["available"] else visibility["rho_nonzero_certified"],
            "gamma": None if not visibility["available"] else ball_record(visibility["gamma"])
        }
    }

    exponents = [int(e) for e in fixture["source_offset_exponents"]]
    points = [_point(q, N, parity, e) for e in exponents]
    if not all(p["full_equals_background_plus_q_atom"] for p in points):
        raise AssertionError("full/background/q-atom Arb reconstruction failed")
    finite_differences = [_finite_difference(q, N, parity, e) for e in exponents]

    counts = {"POSITIVE_CERTIFIED": 0, "NEGATIVE_CERTIFIED": 0, "UNRESOLVED": 0}
    for p in points:
        counts[p["exact_q_effect_sign"]] += 1
    diff_counts = {"POSITIVE_CERTIFIED": 0, "NEGATIVE_CERTIFIED": 0, "UNRESOLVED": 0}
    for p in finite_differences:
        diff_counts[p["sign"]] += 1

    out = {
        "schema_version": "POST169_FB05_SCHUR_VISIBILITY_CERTIFICATE_v2",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_POINT_AND_DIFFERENCE_AUDIT_ONLY",
        "target": target, "precision_bits": precision,
        "threshold": threshold,
        "positive_source_coordinate_points": points,
        "background_central_finite_differences": finite_differences,
        "exact_q_effect_sign_counts": counts,
        "background_difference_sign_counts": diff_counts,
        "nonclaims": [
            "Finite-difference enclosures are not derivative theorems.",
            "The integer shell generator is ray-equivalent, not magnitude-identical, to Lean's intrinsicCubicShellPart.",
            "Pointwise Arb replay is not a whole-cell positivity theorem.",
            "Schur visibility is not FB-05 closure.",
            "RH remains OPEN."
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS", "target": target, "threshold": threshold,
        "exact_q_effect_sign_counts": counts,
        "background_difference_sign_counts": diff_counts,
        "finite_difference_summaries": finite_differences,
        "first_point": points[0], "last_point": points[-1]
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
