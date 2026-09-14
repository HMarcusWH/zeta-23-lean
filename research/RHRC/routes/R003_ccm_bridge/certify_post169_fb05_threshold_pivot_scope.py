#!/usr/bin/env python3
"""Rigorous pointwise Arb replay for post-#169 Schur visibility research.

This certifies finite theorem-aligned [W|c] Schur data only.  It does not claim
a derivative theorem, whole-cell positivity, FB-05 closure, or RH.
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
from post167_fb05_threshold_jet import (
    canonical_entering_atom_arb,
    centered_moment_row,
    von_mangoldt_weight_arb,
)

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
        pivot = H[0, 0]
        return {
            "A": arb_mat(0, 0),
            "b": arb_mat(0, 1),
            "x": arb_mat(0, 1),
            "pivot": pivot,
            "predecessor_pd": positive_definite_certificate(arb_mat(0, 0)),
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
        rho = alpha
        gamma = arb(0)
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
        "predecessor_pd": rec["predecessor_pd"],
    }


def _rank_one_pivot(H: arb_mat, tau: arb, v: list[int]) -> arb | None:
    n = len(v)
    update = arb_mat([[tau * int(v[r]) * int(v[c]) for c in range(n)] for r in range(n)])
    model = H + update
    return _schur_record(model)["pivot"]


def _entrywise_overlap(A: arb_mat, B: arb_mat) -> bool:
    return A.nrows() == B.nrows() and A.ncols() == B.ncols() and all(
        (A[r, c] - B[r, c]).contains(0)
        for r in range(A.nrows())
        for c in range(A.ncols())
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


def _point(q: int, N: int, parity: str, exponent: int) -> dict:
    den = 1 << exponent
    omega = arb(1) / den
    L = arb(q).log() / (1 - omega)
    _W, _c, B, c2 = _step_basis(N, parity)
    full = canonical_source_matrix(L, N + 1, q)
    atom = canonical_entering_atom_arb(q, N + 1, omega)
    background = full - atom
    reconstruction = _entrywise_overlap(full, background + atom)
    Hfull = _restricted(full, B)
    Hbg = _restricted(background, B)
    full_rec = _schur_record(Hfull)
    bg_rec = _schur_record(Hbg)
    v = _moment_vector(N, parity, B)
    order, kappa = _kappa(q, parity)
    tau = kappa * omega ** order
    model_pivot = _rank_one_pivot(Hbg, tau, v) if bg_rec["pivot"] is not None else None
    exact_effect = full_rec["pivot"] - bg_rec["pivot"] if full_rec["pivot"] is not None and bg_rec["pivot"] is not None else None
    model_effect = model_pivot - bg_rec["pivot"] if model_pivot is not None and bg_rec["pivot"] is not None else None
    residual = exact_effect - model_effect if exact_effect is not None and model_effect is not None else None
    return {
        "exponent": exponent,
        "omega": ball_record(omega),
        "L": ball_record(L),
        "full_equals_background_plus_q_atom": reconstruction,
        "H1_background_certified": bool(bg_rec["predecessor_pd"]["certified"]),
        "H1_full_certified": bool(full_rec["predecessor_pd"]["certified"]),
        "background_raw_pivot": None if bg_rec["pivot"] is None else ball_record(bg_rec["pivot"]),
        "background_unit_pivot": None if bg_rec["pivot"] is None else ball_record(bg_rec["pivot"] / c2),
        "full_raw_pivot": None if full_rec["pivot"] is None else ball_record(full_rec["pivot"]),
        "full_unit_pivot": None if full_rec["pivot"] is None else ball_record(full_rec["pivot"] / c2),
        "exact_q_effect": None if exact_effect is None else ball_record(exact_effect),
        "exact_q_effect_sign": _sign_class(exact_effect),
        "rank_one_model_effect": None if model_effect is None else ball_record(model_effect),
        "rank_one_model_effect_sign": _sign_class(model_effect),
        "exact_minus_rank_one": None if residual is None else ball_record(residual),
        "claim_cap": "RIGOROUS_FINITE_POINT_AUDIT_ONLY",
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST169_FB05_SCHUR_VISIBILITY_CERTIFICATE.json"))
    ap.add_argument("--precision-bits", type=int, default=None)
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    target = fixture["target"]
    q = int(target["q"])
    N = int(target["predecessor_N"])
    parity = target["selected_parity"]
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
            "gamma": None if not visibility["available"] else ball_record(visibility["gamma"]),
        },
    }

    points = [_point(q, N, parity, int(e)) for e in fixture["source_offset_exponents"]]
    if not all(p["full_equals_background_plus_q_atom"] for p in points):
        raise AssertionError("full/background/q-atom Arb reconstruction failed")

    counts = {"POSITIVE_CERTIFIED": 0, "NEGATIVE_CERTIFIED": 0, "UNRESOLVED": 0}
    for p in points:
        counts[p["exact_q_effect_sign"]] += 1

    out = {
        "schema_version": "POST169_FB05_SCHUR_VISIBILITY_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_POINT_AUDIT_ONLY",
        "target": target,
        "precision_bits": precision,
        "threshold": threshold,
        "positive_source_coordinate_points": points,
        "exact_q_effect_sign_counts": counts,
        "interpretation": (
            "Arb certifies pointwise one-step Schur geometry and q-atom reconstruction. "
            "No finite-difference quantity is promoted to a derivative theorem."
        ),
        "nonclaims": [
            "The integer shell generator is ray-equivalent, not magnitude-identical, to Lean's intrinsicCubicShellPart.",
            "Pointwise Arb replay is not a whole-cell positivity theorem.",
            "Schur visibility is not FB-05 closure.",
            "No executable result is Lean theorem authority.",
            "RH remains OPEN."
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "target": target,
        "threshold": threshold,
        "exact_q_effect_sign_counts": counts,
        "point_count": len(points)
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
