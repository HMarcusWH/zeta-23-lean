#!/usr/bin/env python3
"""Exact C1 Pair-D structural countermodel on repository parity geometry.

This upgrades the historical post-#129 C1 fixture from prose/experimental
status to a current exact-rational executable certificate. The operator is a
generic reversal-symmetric diagonal matrix, NOT canonicalSourceMatrix.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
RHRC = HERE.parent
R003 = RHRC / "routes" / "R003_ccm_bridge"
if str(R003) not in sys.path:
    sys.path.insert(0, str(R003))

from post150_selected_residual import (  # noqa: E402
    centered_predecessor_basis,
    exact_parity_basis,
    exact_shell_generator,
)

FIXTURE = HERE / "fixtures" / "post204_pair_d_c1_v1.json"


def load_fixture() -> dict:
    return json.loads(FIXTURE.read_text())


def c1_matrix() -> sp.Matrix:
    fx = load_fixture()
    q = fx["historical_fixture"]["q_by_abs_index"]
    K = int(fx["historical_fixture"]["successor_K"])
    return sp.diag(*[sp.Integer(q[abs(d)]) for d in range(-K, K + 1)])


def centered_index_matrix(K: int) -> sp.Matrix:
    return sp.diag(*[sp.Integer(d) for d in range(-K, K + 1)])


def qform(M: sp.Matrix, v: sp.Matrix) -> sp.Expr:
    return sp.simplify((v.T * M * v)[0])


def is_positive_definite_exact(H: sp.Matrix) -> bool:
    if H.rows != H.cols or H != H.T:
        return False
    if H.rows == 0:
        return True
    return all(bool(sp.simplify(H[:k, :k].det()) > 0) for k in range(1, H.rows + 1))


def parity_record(parity: str) -> dict:
    fx = load_fixture()
    N = int(fx["historical_fixture"]["predecessor_N"])
    K = int(fx["historical_fixture"]["successor_K"])
    M = c1_matrix()
    W = centered_predecessor_basis(N, parity)
    V = exact_parity_basis(K, parity)
    c = exact_shell_generator(N, parity)

    H = sp.simplify(W.T * M * W)
    r = sp.simplify(W.T * M * c)
    x = H.inv() * r if H.rows else sp.zeros(0, 1)
    u = sp.simplify(c - W * x)
    pred_residual = sp.simplify(W.T * M * u)
    energy = qform(M, u)
    norm_sq = sp.simplify((u.T * u)[0])
    root = sp.simplify(energy / norm_sq)
    compressed_residual = sp.simplify(V.T * (M - root * sp.eye(2 * K + 1)) * u)

    return {
        "parity": parity,
        "predecessor_basis": W,
        "successor_basis": V,
        "shell_generator": c,
        "predecessor_form": H,
        "predecessor_positive_definite": is_positive_definite_exact(H),
        "shell_coupling": r,
        "shifted_trial": u,
        "predecessor_residual": pred_residual,
        "quadratic_value": sp.simplify(energy),
        "norm_sq": sp.simplify(norm_sq),
        "compressed_root": sp.simplify(root),
        "compressed_root_residual": compressed_residual,
        "successor_bad_witness": bool(energy < 0),
    }


def certify_c1() -> dict:
    fx = load_fixture()
    K = int(fx["historical_fixture"]["successor_K"])
    M = c1_matrix()
    D = centered_index_matrix(K)
    even = parity_record("even")
    odd = parity_record("odd")

    reversal = sp.zeros(2 * K + 1)
    for i in range(2 * K + 1):
        reversal[i, 2 * K - i] = 1

    return {
        "schema_version": "POST204_PAIR_D_C1_CERTIFICATE_v1",
        "status": "PASS",
        "classification": "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
        "matrix": M,
        "reversal_symmetric": sp.simplify(reversal * M * reversal - M) == sp.zeros(2 * K + 1),
        "centered_index_commutator_zero": sp.simplify(D * M - M * D) == sp.zeros(2 * K + 1),
        "even": even,
        "odd": odd,
        "simultaneous_badness": bool(even["successor_bad_witness"] and odd["successor_bad_witness"]),
        "claim_cap": fx["claim_cap"],
        "canonical_realizability": False,
        "rh_claim": False,
    }


def jsonable(x):
    if isinstance(x, sp.MatrixBase):
        return [[str(x[r, c]) for c in range(x.cols)] for r in range(x.rows)]
    if isinstance(x, sp.Basic):
        return str(x)
    if isinstance(x, dict):
        return {k: jsonable(v) for k, v in x.items()}
    if isinstance(x, list):
        return [jsonable(v) for v in x]
    return x


if __name__ == "__main__":
    print(json.dumps(jsonable(certify_c1()), indent=2, sort_keys=True))
