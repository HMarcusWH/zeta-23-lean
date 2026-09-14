#!/usr/bin/env python3
"""Deterministic acceptance checks for post-#169 Schur visibility tooling."""
from __future__ import annotations

import json
import math

import numpy as np
import sympy as sp

from canonical_source_numeric import canonical_source_matrix_L
from post150_selected_residual import evaluate_selected_residual_state, exact_parity_basis
from post167_fb05_threshold_jet import centered_moment_row, normalized_source_series_coefficient_sympy
from post169_fb05_schur_visibility import (
    directional_schur_derivative_float,
    full_background_at_omega_float,
    one_step_geometry,
    rank_one_pivot_update_float,
    schur_pivot_float,
    theorem_aligned_pivot_float,
)


def _exact_pivot(H: sp.Matrix) -> sp.Expr:
    if H.rows == 1:
        return H[0, 0]
    A = H[:-1, :-1]
    b = H[:-1, -1]
    d = H[-1, -1]
    return sp.simplify(d - (b.T * A.inv() * b)[0, 0])


def _symbolic_rank_one_check() -> None:
    A = sp.Matrix([[3, 1], [1, 2]])
    b = sp.Matrix([1, 2])
    H = A.row_join(b).col_join(sp.Matrix([[1, 2, 5]]))
    v = sp.Matrix([2, -1, 3])
    t = sp.symbols("t")
    P = _exact_pivot(H)
    a = v[:-1, :]
    alpha = v[-1, 0]
    x = A.inv() * b
    rho = sp.simplify(alpha - (a.T * x)[0, 0])
    gamma = sp.simplify((a.T * A.inv() * a)[0, 0])
    lhs = _exact_pivot(H + t * (v * v.T))
    rhs = sp.simplify(P + t * rho**2 / (1 + t * gamma))
    if sp.simplify(lhs - rhs) != 0:
        raise AssertionError("exact rank-one Schur update identity failed")

    D = sp.Matrix([[2, 1, -1], [1, -1, 2], [-1, 2, 3]])
    deriv_exact = sp.simplify(sp.diff(_exact_pivot(H + t * D), t).subs(t, 0))
    DA = D[:-1, :-1]
    Db = D[:-1, -1]
    Dd = D[-1, -1]
    deriv_formula = sp.simplify(Dd - 2 * (Db.T * x)[0, 0] + (x.T * DA * x)[0, 0])
    if sp.simplify(deriv_exact - deriv_formula) != 0:
        raise AssertionError("exact directional Schur derivative identity failed")


def _geometry_and_jet_checks() -> list[dict]:
    records = []
    for N in range(1, 8):
        K = N + 1
        for parity in ("odd", "even"):
            geom = one_step_geometry(N, parity)
            V = exact_parity_basis(K, parity)
            B = geom.step_basis_exact
            if B.cols != V.cols or B.rank() != V.cols:
                raise AssertionError("[W|c] does not have successor-carrier dimension")
            if sp.Matrix.hstack(V, B).rank() != V.cols:
                raise AssertionError("[W|c] does not span exact successor carrier")
            if geom.W_exact.T * geom.c_exact != sp.zeros(geom.W_exact.cols, 1):
                raise AssertionError("W/c orthogonality regression")

            if parity == "odd":
                first_k = 3
                moment_order = 3
                expected_scale = sp.Rational(-2, math.factorial(7))
            else:
                first_k = 4
                moment_order = 4
                expected_scale = sp.Rational(2, math.factorial(9))

            for k in range(first_k):
                C = normalized_source_series_coefficient_sympy(K, k)
                R = sp.simplify(B.T * C * B)
                if R != sp.zeros(R.rows, R.cols):
                    raise AssertionError(f"unexpected pre-leading threshold jet N={N} parity={parity} k={k}")
            C = normalized_source_series_coefficient_sympy(K, first_k)
            R = sp.simplify(B.T * C * B)
            m = centered_moment_row(K, B, moment_order)
            expected = sp.simplify(expected_scale * (m.T * m))
            if sp.simplify(R - expected) != sp.zeros(R.rows, R.cols):
                raise AssertionError(f"threshold moment rank-one law failed in [W|c], N={N}, parity={parity}")
            records.append({"N": N, "Kstar": K, "parity": parity, "dimension": B.cols})
    return records


def _production_pivot_agreement() -> list[dict]:
    cases = [
        (2, 0.75, 2, "even"),
        (2, 0.75, 2, "odd"),
        (3, 1.25, 3, "even"),
        (3, 1.25, 3, "odd"),
    ]
    out = []
    for Q, L, N, parity in cases:
        legacy = evaluate_selected_residual_state(Q, L, N, parity)
        M = canonical_source_matrix_L(L, N + 1)
        rec = theorem_aligned_pivot_float(M, N, parity)
        got = rec["unit_shell_pivot"]
        want = float(legacy["selected_residual"]["schur_energy"])
        err = abs(got - want)
        scale = max(abs(got), abs(want), 1.0)
        if err > 5e-11 * scale:
            raise AssertionError(f"unit-shell Schur mismatch Q={Q} L={L} N={N} {parity}: {err}")
        out.append({"Q": Q, "L": L, "N": N, "parity": parity, "error": err})
    return out


def _background_reconstruction_check() -> float:
    rec = full_background_at_omega_float(17, 3, 2.0 ** -10)
    rebuilt = rec["background"] + rec["signed_q_atom"]
    err = float(np.max(np.abs(rebuilt - rec["full"])))
    if err > 2e-12:
        raise AssertionError(f"background + q atom reconstruction drift: {err}")
    return err


def _float_formula_smoke() -> None:
    H = np.array([[3.0, 1.0, 1.0], [1.0, 2.0, 2.0], [1.0, 2.0, 5.0]])
    v = np.array([2.0, -1.0, 3.0])
    tau = 0.03125
    base = schur_pivot_float(H)
    a = v[:-1]
    alpha = v[-1]
    x = base["x"]
    rho = float(alpha - a @ x)
    gamma = float(a @ np.linalg.solve(base["A"], a))
    predicted = rank_one_pivot_update_float(base["pivot"], tau, rho, gamma)
    actual = schur_pivot_float(H + tau * np.outer(v, v))["pivot"]
    if abs(predicted - actual) > 2e-13:
        raise AssertionError("floating rank-one update smoke failed")
    D = np.array([[2.0, 1.0, -1.0], [1.0, -1.0, 2.0], [-1.0, 2.0, 3.0]])
    analytic = directional_schur_derivative_float(H, D)
    eps = 1e-6
    finite = (schur_pivot_float(H + eps * D)["pivot"] - schur_pivot_float(H - eps * D)["pivot"]) / (2 * eps)
    if abs(analytic - finite) > 2e-8:
        raise AssertionError("floating directional derivative smoke failed")


def main() -> int:
    _symbolic_rank_one_check()
    _float_formula_smoke()
    geometry = _geometry_and_jet_checks()
    production = _production_pivot_agreement()
    reconstruction_error = _background_reconstruction_check()
    payload = {
        "schema_version": "POST169_FB05_SCHUR_VISIBILITY_CHECK_v1",
        "status": "PASS",
        "claim_cap": "EXACT_EXECUTABLE_ALGEBRA_ONLY",
        "checks": {
            "exact_rank_one_schur_update": True,
            "exact_directional_schur_derivative": True,
            "step_basis_spans_successor": True,
            "step_basis_threshold_moment_law": True,
            "unit_shell_pivot_matches_post150_selected_residual": True,
            "background_plus_entering_atom_reconstructs_full": True,
        },
        "geometry_records": geometry,
        "production_pivot_agreement": production,
        "max_background_reconstruction_error": reconstruction_error,
        "nonclaims": [
            "The exact integer shell generator is not asserted magnitude-identical to Lean's intrinsicCubicShellPart.",
            "Executable algebra is not Lean theorem authority.",
            "No aperture positivity or RH conclusion is claimed.",
            "RH remains OPEN."
        ]
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
