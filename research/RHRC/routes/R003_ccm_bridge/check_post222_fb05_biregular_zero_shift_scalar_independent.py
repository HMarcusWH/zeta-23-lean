#!/usr/bin/env python3
"""Independent algebra-path check for the post-#222 scalar evaluator.

This checker deliberately rebuilds the cubic geometry and [W|c] Schur blocks
without calling the primary geometry constructor.  It then compares those
results with the primary evaluator by zero-containing Arb residuals.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp
from flint import arb, arb_mat

from canonical_source_arb import ball_record, set_precision, to_arb_rational
from post150_selected_residual import (
    centered_predecessor_basis,
    exact_parity_basis,
    exact_shell_generator,
)
from post166_fb05_cell_interval import cell_coordinate_L_arb, fixed_q_canonical_source_matrix_arb
from post222_fb05_biregular_zero_shift_scalar import (
    biregular_zero_shift_geometry_exact,
    transfer_coefficients,
    zero_shift_response_record,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post222_fb05_biregular_zero_shift_scalar_v1.json"


def _arbq(x: sp.Expr) -> arb:
    q = sp.Rational(x)
    return to_arb_rational(int(q.p), int(q.q))


def _arbmat(A: sp.Matrix) -> arb_mat:
    if A.cols == 0:
        return arb_mat(A.rows, 0)
    return arb_mat([[_arbq(A[r, c]) for c in range(A.cols)] for r in range(A.rows)])


def _indices(K: int) -> list[int]:
    return list(range(-K, K + 1))


def _project(B: sp.Matrix, v: sp.Matrix) -> sp.Matrix:
    G = B.T * B
    if G.det() == 0:
        raise AssertionError("independent projection Gram matrix singular")
    return sp.simplify(B * G.inv() * B.T * v)


def _independent_geometry(N: int) -> dict[str, sp.Matrix]:
    K = N + 1
    Vodd = exact_parity_basis(K, "odd")
    Veven = exact_parity_basis(K, "even")
    raw3 = sp.Matrix([sp.Integer(n) ** 3 for n in _indices(K)])
    g_minus = _project(Vodd, raw3)

    D = sp.diag(*_indices(K))
    sol, params = (D * Veven).gauss_jordan_solve(g_minus)
    if params.rows != 0:
        raise AssertionError("independent D pullback not unique")
    g_plus = sp.simplify(Veven * sol)

    out = {"g_minus": g_minus}
    for parity, g in (("even", g_plus), ("odd", g_minus)):
        s = exact_shell_generator(N, parity)
        c = sp.simplify(((s.T * g)[0] / (s.T * s)[0]) * s)
        out[f"c_{parity}"] = c

    out["d"] = sp.simplify(D * out["c_even"] - out["c_odd"])
    out["a"] = sp.simplify(g_minus - out["c_odd"])
    return out


def _slice(H: arb_mat, r0: int, r1: int, c0: int, c1: int) -> arb_mat:
    return arb_mat([[H[r, c] for c in range(c0, c1)] for r in range(r0, r1)])


def _dot(x: arb_mat, y: arb_mat) -> arb:
    return (x.transpose() * y)[0, 0]


def _independent_response(M: arb_mat, W: sp.Matrix, c: sp.Matrix) -> dict:
    C = sp.Matrix.hstack(W, c)
    Cb = _arbmat(C)
    H = Cb.transpose() * M * Cb
    m = W.cols
    A = _slice(H, 0, m, 0, m) if m else arb_mat(0, 0)
    b = _slice(H, 0, m, m, m + 1) if m else arb_mat(0, 1)
    q = H[m, m]
    if m:
        y = A.solve(b)
        x = _arbmat(W) * y
        schur = q - (b.transpose() * y)[0, 0]
    else:
        y = arb_mat(0, 1)
        x = arb_mat([[arb(0)] for _ in range(c.rows)])
        schur = q
    cb = _arbmat(c)
    u = cb - x
    norm = _dot(cb, cb)
    return {"sigma": schur / norm, "x": x, "u": u}


def _n2_exact(K: int) -> sp.Matrix:
    inds = _indices(K)
    ones = sp.ones(2 * K + 1, 1)
    d2 = sp.Matrix([sp.Integer(n) ** 2 for n in inds])
    return sp.simplify(d2 - ((ones.T * d2)[0] / (ones.T * ones)[0]) * ones)


def _contains_zero(x: arb) -> bool:
    return bool(x.contains(0))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    args = ap.parse_args()

    fx = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    set_precision(int(fx["implementation_check_precision_bits"]))
    N = int(fx["selected_target"]["predecessor_N"])
    K = N + 1

    independent = _independent_geometry(N)
    primary_geom = biregular_zero_shift_geometry_exact(N)
    assert independent["c_even"] == primary_geom.c_plus
    assert independent["c_odd"] == primary_geom.c_minus
    assert independent["d"] == primary_geom.d
    assert independent["a"] == primary_geom.a
    assert independent["g_minus"] == primary_geom.g_minus

    rows = []
    for point in schedule["points"]:
        Q = int(point["Q"])
        t = arb(int(point["t_num"])) / int(point["t_den"])
        L = cell_coordinate_L_arb(Q, t)
        M = fixed_q_canonical_source_matrix_arb(L, K, Q)

        pplus = zero_shift_response_record(M, primary_geom.W_plus, primary_geom.c_plus)
        pminus = zero_shift_response_record(M, primary_geom.W_minus, primary_geom.c_minus)
        iplus = _independent_response(M, centered_predecessor_basis(N, "even"), independent["c_even"])
        iminus = _independent_response(M, centered_predecessor_basis(N, "odd"), independent["c_odd"])

        rs_plus = pplus["sigma"] - iplus["sigma"]
        rs_minus = pminus["sigma"] - iminus["sigma"]
        if not _contains_zero(rs_plus) or not _contains_zero(rs_minus):
            raise AssertionError("independent [W|c] Schur reconstruction mismatch")

        coeff_primary = transfer_coefficients(pminus["x"], pminus["u"], primary_geom)
        cb = _arbmat(independent["c_odd"])
        db = _arbmat(independent["d"])
        ab = _arbmat(independent["a"])
        gb = _arbmat(independent["g_minus"])
        den = _dot(cb, cb)
        alpha_i = arb(1) - _dot(iminus["x"], db) / den
        gamma_i = arb(1) - _dot(iminus["x"], ab) / den
        gamma_overlap_i = _dot(iminus["u"], gb) / den

        for name, residual in (
            ("alpha", coeff_primary["alpha0"] - alpha_i),
            ("Gamma", coeff_primary["gamma0"] - gamma_i),
            ("Gamma_overlap", gamma_i - gamma_overlap_i),
        ):
            if not residual.contains(0):
                raise AssertionError(f"independent {name} reconstruction mismatch")

        n2 = _arbmat(_n2_exact(K))
        mu_i = (n2.transpose() * M * iplus["u"])[0, 0] / _dot(n2, n2)
        transferred_i = alpha_i * iplus["sigma"] + gamma_i * mu_i
        scalar_residual = iminus["sigma"] - transferred_i
        if not scalar_residual.contains(0):
            raise AssertionError("independent scalar transfer mismatch")

        rows.append({
            "label": point["label"],
            "Q": Q,
            "sigma_plus_residual": ball_record(rs_plus),
            "sigma_minus_residual": ball_record(rs_minus),
            "alpha_residual": ball_record(coeff_primary["alpha0"] - alpha_i),
            "Gamma_residual": ball_record(coeff_primary["gamma0"] - gamma_i),
            "Gamma_overlap_residual": ball_record(gamma_i - gamma_overlap_i),
            "transfer_residual": ball_record(scalar_residual),
        })

    out = {
        "status": "PASS",
        "schema_version": "POST222_FB05_BIREGULAR_ZERO_SHIFT_SCALAR_INDEPENDENT_v1",
        "point_count": len(rows),
        "rows": rows,
        "claim_cap": "IMPLEMENTATION_CROSS_CHECK_ONLY",
        "theorem_promotion": False,
        "rh_claim": False,
    }
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
