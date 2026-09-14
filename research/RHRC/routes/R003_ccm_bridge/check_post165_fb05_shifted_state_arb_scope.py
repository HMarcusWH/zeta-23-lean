#!/usr/bin/env python3
"""Rigorous Arb checks for the post-#165 shifted-state machinery.

A production first-bad state is conditional and need not occur in a finite
scan.  This check therefore has two deliberately separate roles:

1. exercise the generalized shifted system on a narrow safe negative interval
   around lambda=-1 without asserting that the interval contains a secular
   root;
2. Arb-audit the closest-to-zero H1 successor found by the floating #166 scout
   using an exact Sylvester positive-definiteness certificate.  Failure to
   certify positivity is reported as UNRESOLVED, not converted into a bad-state
   claim.

The shifted smoke validates only numerical/certification plumbing:
  * H - Lambda G is solved in the exact integer predecessor basis;
  * the predecessor residual encloses zero entrywise;
  * on the even smoke state, the exact quadratic-normal source moment and its
    signed channel reconstruction overlap;
  * the scalar identity-shift channel vanishes in the mixed pairing;
  * the existing #165 Arb S8 evaluator is callable on the same aperture.

No root, whole-cell sign theorem, sourceMoment/M4 implication, or RH conclusion
is promoted by this file.
"""
from __future__ import annotations

import json

import sympy as sp
from flint import arb, arb_mat

from canonical_riesz_endpoint_scalar import (
    canonical_riesz_endpoint_scalar_arb,
    sign_classification_arb,
)
from canonical_source_arb import (
    ball_record,
    canonical_source_matrix,
    fixed_cell_membership,
    set_precision,
    signed_channel_matrices,
    to_arb_rational,
)
from certify_post150_selected_residual_scope import positive_definite_certificate
from post150_selected_residual import (
    centered_predecessor_basis,
    exact_parity_basis,
    exact_shell_generator,
)


def _arb_matrix_from_sympy(A: sp.Matrix) -> arb_mat:
    if A.cols == 0:
        return arb_mat(A.rows, 0)
    return arb_mat([[int(A[r, c]) for c in range(A.cols)] for r in range(A.rows)])


def _scalar(A: arb_mat) -> arb:
    if A.nrows() != 1 or A.ncols() != 1:
        raise ValueError("expected 1x1 matrix")
    return A[0, 0]


def _restriction(M: arb_mat, B: sp.Matrix) -> arb_mat:
    if B.cols == 0:
        return arb_mat(0, 0)
    X = _arb_matrix_from_sympy(B)
    return X.transpose() * M * X


def _quadratic_normal_column(K: int) -> arb_mat:
    d = list(range(-K, K + 1))
    dim = len(d)
    sum2 = sum(x * x for x in d)
    return arb_mat(
        [[to_arb_rational(dim * x * x - sum2, dim)] for x in d]
    )


def _all_contain_zero(v: arb_mat) -> bool:
    return all(v[r, c].contains(0) for r in range(v.nrows()) for c in range(v.ncols()))


def _safe_interval_shift_case(Q: int, L_num: int, L_den: int, N: int, parity: str) -> dict:
    K = N + 1
    L = to_arb_rational(L_num, L_den)
    M = canonical_source_matrix(L, K, Q)
    W = centered_predecessor_basis(N, parity)
    c = exact_shell_generator(N, parity)
    Wb = _arb_matrix_from_sympy(W)
    cb = _arb_matrix_from_sympy(c)

    H = Wb.transpose() * M * Wb if W.cols else arb_mat(0, 0)
    G = Wb.transpose() * Wb if W.cols else arb_mat(0, 0)
    r = Wb.transpose() * M * cb if W.cols else arb_mat(0, 1)

    # Exercise the same interval constructor and interval solve used by the
    # root replay, but around a known-safe negative shift rather than pretending
    # this is a root bracket.
    lam = arb("-1", "1/1099511627776")
    if W.cols:
        x = (H - G * lam).solve(r)
        u = cb - Wb * x
    else:
        u = cb

    residual = M * u - u * lam
    pred_residual = Wb.transpose() * residual if W.cols else arb_mat(0, 1)
    pred_overlap = _all_contain_zero(pred_residual)

    s8 = canonical_riesz_endpoint_scalar_arb(8, Q, L)
    record = {
        "Q": Q,
        "L_num": L_num,
        "L_den": L_den,
        "N": N,
        "Kstar": K,
        "parity": parity,
        "lambda_interval": ball_record(lam),
        "predecessor_residual_contains_zero_entrywise": pred_overlap,
        "S8": ball_record(s8),
        "S8_sign": sign_classification_arb(s8),
    }

    if parity == "even":
        n2 = _quadratic_normal_column(K)
        den = _scalar(n2.transpose() * n2)
        direct = _scalar(n2.transpose() * M * u) / den
        channels = signed_channel_matrices(L, K, Q)
        channel_values = {}
        total = arb(0)
        scalar_shift = None
        for name, A in channels.items():
            value = _scalar(n2.transpose() * A * u) / den
            channel_values[name] = ball_record(value)
            total += value
            if name == "scalar_shift":
                scalar_shift = value
        delta = total - direct
        m4 = arb(0)
        for row, d in enumerate(range(-K, K + 1)):
            m4 += (d**4) * u[row, 0]
        record["even_observables"] = {
            "M4": ball_record(m4),
            "explicitCanonicalSourceMoment": ball_record(direct),
            "source_channels": channel_values,
            "channel_reconstruction_difference": ball_record(delta),
            "channel_reconstruction_overlap": bool(delta.contains(0)),
            "scalar_shift_contains_zero": bool(
                scalar_shift is not None and scalar_shift.contains(0)
            ),
        }
        if not record["even_observables"]["channel_reconstruction_overlap"]:
            raise AssertionError("Arb source-moment channels do not reconstruct direct moment")
        if not record["even_observables"]["scalar_shift_contains_zero"]:
            raise AssertionError("identity scalar shift did not vanish in even mixed pairing")

    if not pred_overlap:
        raise AssertionError("Arb shifted predecessor residual does not enclose zero")
    return record


def _near_critical_successor_case(
    Q: int,
    L_num: int,
    L_den: int,
    N: int,
    parity: str,
    floating_min_eigenvalue: float,
) -> dict:
    """Arb-classify one exact sampled successor without assuming its sign."""
    K = N + 1
    L = to_arb_rational(L_num, L_den)
    cell = fixed_cell_membership(Q, L)
    Vsucc = exact_parity_basis(K, parity)
    Msucc = canonical_source_matrix(L, K, Q)
    Hsucc = _restriction(Msucc, Vsucc)
    pd = positive_definite_certificate(Hsucc)
    classification = "POSITIVE_DEFINITE_CERTIFIED" if pd["certified"] else "UNRESOLVED"
    return {
        "Q": Q,
        "L_num": L_num,
        "L_den": L_den,
        "N": N,
        "Kstar": K,
        "parity": parity,
        "floating_min_form_eigenvalue": floating_min_eigenvalue,
        "cell": cell,
        "classification": classification,
        "strict_positive_form": pd,
        "nonclaim": (
            "This certifies only the exact sampled finite successor when classification "
            "is POSITIVE_DEFINITE_CERTIFIED; it is not a whole-cell positivity theorem."
        ),
    }


def main() -> int:
    set_precision(256)
    cases = [
        _safe_interval_shift_case(2, 3, 4, 2, "even"),
        _safe_interval_shift_case(3, 5, 4, 2, "odd"),
    ]
    # Strongest near-critical signal emitted by the 672-state #166 scout.
    near_critical = _near_critical_successor_case(
        16,
        3098486646606,
        1099511627776,
        3,
        "odd",
        2.3292865177849273e-12,
    )
    payload = {
        "schema_version": "POST165_FB05_SHIFTED_ARB_CHECK_v2",
        "status": "PASS",
        "cases": cases,
        "near_critical_successor": near_critical,
        "claim_firewall": {
            "root_claim": False,
            "whole_cell_claim": False,
            "theorem_authority": False,
            "terminal_claim": "RH_OPEN",
        },
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
