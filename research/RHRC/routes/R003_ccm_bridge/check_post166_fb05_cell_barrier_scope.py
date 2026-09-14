#!/usr/bin/env python3
"""Deterministic plumbing check for the post-#166 Q=16 cell barrier audit."""
from __future__ import annotations

import json
import math

from flint import arb_mat

from canonical_source_arb import canonical_source_matrix, set_precision, to_arb_rational
from post150_selected_residual import exact_parity_basis
from post166_fb05_cell_interval import (
    _arb_matrix_from_sympy,
    classify_principal_minors,
    fixed_q_canonical_source_matrix_arb,
    principal_determinants_arb,
    successor_barrier_float,
)

Q = 16
N = 3
K = 4
PARITY = "odd"
L_NUM = 3098486646606
L_DEN = 1099511627776


def _entrywise_overlap(A: arb_mat, B: arb_mat) -> bool:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        return False
    return all((A[r, c] - B[r, c]).contains(0) for r in range(A.nrows()) for c in range(A.ncols()))


def main() -> int:
    set_precision(256)
    L = to_arb_rational(L_NUM, L_DEN)
    direct = canonical_source_matrix(L, K, Q)
    fixed = fixed_q_canonical_source_matrix_arb(L, K, Q)
    if not _entrywise_overlap(direct, fixed):
        raise AssertionError("fixed-Q continuation does not overlap production matrix at interior seed")

    B = exact_parity_basis(K, PARITY)
    Bb = _arb_matrix_from_sympy(B)
    H = Bb.transpose() * fixed * Bb
    minors = principal_determinants_arb(H)
    classification = classify_principal_minors(minors)
    if classification != "POSITIVE_CERTIFIED":
        raise AssertionError(f"#166 near-critical seed lost its rigorous positive classification: {classification}")

    Lf = L_NUM / L_DEN
    t = (Lf - math.log(Q)) / (math.log(Q + 1) - math.log(Q))
    floating = successor_barrier_float(Q, N, PARITY, t)
    if floating["dimension"] != 3:
        raise AssertionError("expected 3-dimensional odd successor restriction")
    if not floating["min_eigenvalue"] > 0:
        raise AssertionError("near-critical floating seed unexpectedly became non-positive")

    payload = {
        "schema_version": "POST166_FB05_CELL_BARRIER_CHECK_v1",
        "status": "PASS",
        "target": {"Q": Q, "N": N, "Kstar": K, "parity": PARITY},
        "seed": {
            "L_num": L_NUM,
            "L_den": L_DEN,
            "t": t,
            "fixed_q_matches_production_entrywise": True,
            "arb_classification": classification,
            "leading_principal_minors": [x.str(30, more=True) for x in minors],
            "floating_min_eigenvalue": floating["min_eigenvalue"],
            "normalized_min_eigenvalue": floating["normalized_min_eigenvalue"],
            "orthonormal_normalized_determinant": floating["orthonormal_normalized_determinant"],
        },
        "claim_firewall": {
            "whole_cell_claim": False,
            "theorem_authority": False,
            "terminal_claim": "RH_OPEN",
        },
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
