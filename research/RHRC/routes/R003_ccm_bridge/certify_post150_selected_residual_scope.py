#!/usr/bin/env python3
"""Rigorous replay of post-#150 selected-residual falsification candidates.

A candidate counts toward E4A4-SCHUR-FB-04 only when every advertised
hypothesis and the negative selected-residual sign are enclosed by Arb balls.

The strongest scope implemented here is H3:
  * selected predecessor positive definite (hence regular),
  * selected successor parity has an explicit negative rational direction,
  * every smaller size in both parities is certified positive definite at the
    same aperture,
  * the exact one-step shell trial has strictly negative canonical energy.

This is intentionally *not* whole-cell ancestry. Positive definiteness is a
stronger finite sufficient condition for the nonnegative smaller-size
hypotheses exported by #150.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp
from flint import arb, arb_mat

from canonical_source_arb import (
    ball_record,
    canonical_source_matrix,
    definitely_negative,
    definitely_nonzero,
    definitely_positive,
    fixed_cell_membership,
    set_precision,
    signed_channel_matrices,
    to_arb_rational,
)
from post150_selected_residual import (
    centered_predecessor_basis,
    exact_parity_basis,
    exact_shell_generator,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post150_selected_residual_v1.json"


def _arb_matrix_from_sympy(A: sp.Matrix) -> arb_mat:
    if A.cols == 0:
        return arb_mat(A.rows, 0)
    return arb_mat([[int(A[r, c]) for c in range(A.cols)] for r in range(A.rows)])


def _column(values: list[int]) -> arb_mat:
    return arb_mat([[int(v)] for v in values])


def _scalar(A: arb_mat) -> arb:
    if A.nrows() != 1 or A.ncols() != 1:
        raise ValueError("expected 1x1 matrix")
    return A[0, 0]


def _quadratic(H: arb_mat, v: arb_mat) -> arb:
    return _scalar(v.transpose() * H * v)


def _leading_principal(H: arb_mat, k: int) -> arb_mat:
    return arb_mat([[H[r, c] for c in range(k)] for r in range(k)])


def positive_definite_certificate(H: arb_mat) -> dict:
    if H.nrows() != H.ncols():
        raise ValueError("positive-definite check requires square matrix")
    if H.nrows() == 0:
        return {
            "certified": True,
            "dimension": 0,
            "criterion": "vacuous_zero_dimensional",
            "leading_principal_minors": [],
        }
    minors = []
    ok = True
    for k in range(1, H.nrows() + 1):
        det = _leading_principal(H, k).det()
        pos = definitely_positive(det)
        minors.append({"k": k, "det": ball_record(det), "positive": pos})
        ok = ok and pos
    return {
        "certified": ok,
        "dimension": H.nrows(),
        "criterion": "Sylvester_leading_principal_minors",
        "leading_principal_minors": minors,
    }


def matrix_difference_contains_zero(A: arb_mat, B: arb_mat) -> dict:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        raise ValueError("shape mismatch")
    failures = []
    for r in range(A.nrows()):
        for c in range(A.ncols()):
            d = A[r, c] - B[r, c]
            if not d.contains(0):
                failures.append({"row": r, "col": c, "difference": ball_record(d)})
    return {"certified_overlap_entrywise": not failures, "failures": failures}


def _restriction(M: arb_mat, B: sp.Matrix) -> arb_mat:
    if B.cols == 0:
        return arb_mat(0, 0)
    X = _arb_matrix_from_sympy(B)
    return X.transpose() * M * X


def certify_smaller_sizes(Q: int, L: arb, predecessor_N: int) -> dict:
    rows = []
    ok = True
    for M in range(predecessor_N + 1):
        source = canonical_source_matrix(L, M, Q)
        for parity in ("even", "odd"):
            V = exact_parity_basis(M, parity)
            H = _restriction(source, V)
            cert = positive_definite_certificate(H)
            rows.append({"size": M, "parity": parity, "strict_positive_form": cert})
            ok = ok and cert["certified"]
    return {
        "certified": ok,
        "meaning": (
            "Every smaller parity carrier is positive definite at the selected "
            "aperture; this is stronger than the H3 no-ParityBad requirement."
        ),
        "rows": rows,
    }


def _channel_energy_records(Q: int, L: arb, K: int, u: arb_mat, total_direct: arb) -> dict:
    channels = signed_channel_matrices(L, K, Q)
    records = {}
    total = arb(0)
    for name, A in channels.items():
        e = _quadratic(A, u)
        records[name] = ball_record(e)
        total += e
    delta = total - total_direct
    return {
        "signed_channels": records,
        "sum": ball_record(total),
        "direct_total": ball_record(total_direct),
        "reconstruction_difference": ball_record(delta),
        "reconstruction_overlap": bool(delta.contains(0)),
    }


def certify_candidate(candidate: dict, precision_bits: int) -> dict:
    set_precision(precision_bits)

    Q = int(candidate["Q"])
    N = int(candidate["N"])
    K = N + 1
    parity = candidate["parity"]
    num = int(candidate["L_num"])
    den = int(candidate["L_den"])
    L = to_arb_rational(num, den)

    cell = fixed_cell_membership(Q, L)
    if not cell["certified"]:
        return {
            "candidate": candidate,
            "certified": False,
            "failure": "aperture_not_certified_in_fixed_cell",
            "cell": cell,
        }

    Vprev = exact_parity_basis(N, parity)
    W = centered_predecessor_basis(N, parity)
    Vsucc = exact_parity_basis(K, parity)
    c_exact = exact_shell_generator(N, parity)

    Mprev = canonical_source_matrix(L, N, Q)
    Msucc = canonical_source_matrix(L, K, Q)

    Hprev = _restriction(Mprev, Vprev)
    H = _restriction(Msucc, W)
    flow = matrix_difference_contains_zero(H, Hprev)

    predecessor_pd = positive_definite_certificate(H)
    detH = H.det() if H.nrows() else arb(1)
    regular = definitely_nonzero(detH)

    Hsucc = _restriction(Msucc, Vsucc)
    witness_coeffs = candidate.get("bad_witness_coeffs_in_exact_successor_basis")
    if witness_coeffs is None:
        successor_bad = {"certified": False, "failure": "missing_rational_successor_bad_witness"}
    elif len(witness_coeffs) != Vsucc.cols:
        successor_bad = {
            "certified": False,
            "failure": "bad_witness_dimension_mismatch",
            "expected": Vsucc.cols,
            "got": len(witness_coeffs),
        }
    else:
        y = _column([int(x) for x in witness_coeffs])
        qbad = _quadratic(Hsucc, y)
        successor_bad = {
            "certified": definitely_negative(qbad),
            "witness_coeffs": [int(x) for x in witness_coeffs],
            "quadratic_value": ball_record(qbad),
        }

    smaller = certify_smaller_sizes(Q, L, N)

    Wb = _arb_matrix_from_sympy(W)
    cb = _arb_matrix_from_sympy(c_exact)

    if W.cols:
        r = Wb.transpose() * Msucc * cb
        if not regular:
            schur = {"certified": False, "failure": "predecessor_not_certified_regular"}
            direct_energy = None
            u = None
        else:
            x = H.solve(r)
            q_shell = _quadratic(Msucc, cb)
            rx = _scalar(r.transpose() * x)
            schur_energy = q_shell - rx
            u = cb - Wb * x
            direct_energy = _quadratic(Msucc, u)
            identity_delta = direct_energy - schur_energy
            schur = {
                "certified": (
                    definitely_negative(schur_energy)
                    and definitely_negative(direct_energy)
                    and identity_delta.contains(0)
                ),
                "shell_energy": ball_record(q_shell),
                "pairing_correction": ball_record(rx),
                "schur_energy": ball_record(schur_energy),
                "direct_trial_energy": ball_record(direct_energy),
                "identity_difference": ball_record(identity_delta),
                "identity_overlap": bool(identity_delta.contains(0)),
            }
    else:
        q_shell = _quadratic(Msucc, cb)
        u = cb
        direct_energy = q_shell
        schur = {
            "certified": definitely_negative(q_shell),
            "shell_energy": ball_record(q_shell),
            "pairing_correction": ball_record(arb(0)),
            "schur_energy": ball_record(q_shell),
            "direct_trial_energy": ball_record(q_shell),
            "identity_difference": ball_record(arb(0)),
            "identity_overlap": True,
        }

    H0 = cell["certified"] and regular
    H1 = H0 and predecessor_pd["certified"]
    H2 = H1 and successor_bad["certified"]
    H3 = H2 and smaller["certified"]
    sign_violation = H3 and schur["certified"]

    channels = (
        _channel_energy_records(Q, L, K, u, direct_energy)
        if u is not None and direct_energy is not None
        else None
    )

    result = {
        "candidate": {"Q": Q, "L_num": num, "L_den": den, "N": N, "Kstar": K, "parity": parity},
        "precision_bits": precision_bits,
        "cell": cell,
        "geometry": {
            "predecessor_dimension": W.cols,
            "successor_dimension": Vsucc.cols,
            "shell_generator": [int(x) for x in c_exact],
            "shell_normalization": (
                "exact integer generator of W^perp inside the one-dimensional "
                "successor parity shell; sign-equivalent, not magnitude-identical, "
                "to intrinsicCubicShellPart"
            ),
        },
        "n_flow_restriction_agreement": flow,
        "predecessor": {
            "determinant": ball_record(detH),
            "regular": regular,
            "positive_definite": predecessor_pd,
        },
        "successor_badness": successor_bad,
        "same_aperture_smaller_size_ancestry": smaller,
        "selected_residual": schur,
        "channels": channels,
        "scope": {
            "H0_regular": H0,
            "H1_predecessor_positive": H1,
            "H2_selected_successor_bad": H2,
            "H3_all_smaller_sizes_both_parities_good_same_aperture": H3,
        },
        "fb04_scoped_counterexample_certified": sign_violation,
        "whole_cell_ancestry_certified": False,
        "claim_cap": (
            "RIGOROUS_FINITE_NUMERICAL_COUNTEREXAMPLE_TO_H3_SCOPED_SIGN_MECHANISM"
            if sign_violation
            else "RIGOROUS_FINITE_NUMERICAL_AUDIT_ONLY"
        ),
        "nonclaims": [
            "No whole-cell #150 ancestry is certified by this calculation.",
            "No numerical result is Lean theorem authority.",
            "No finite-to-infinite closure or RH claim follows.",
            "RH remains OPEN.",
        ],
    }
    result["certified"] = bool(
        cell["certified"]
        and flow["certified_overlap_entrywise"]
        and channels is not None
        and channels["reconstruction_overlap"]
    )
    return result


def load_candidates(path: Path) -> tuple[dict, list[dict]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if "candidates" in payload:
        return payload, list(payload["candidates"])
    if "top_negative_candidates" in payload:
        return payload, list(payload["top_negative_candidates"])
    if {"Q", "N", "parity", "L_num", "L_den"} <= payload.keys():
        return {"schema_version": "single_candidate"}, [payload]
    raise ValueError("input does not contain recognizable candidates")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST150_SELECTED_RESIDUAL_CERTIFICATE.json"))
    ap.add_argument("--precision-bits", type=int, default=192)
    ap.add_argument("--candidate-index", type=int, default=None)
    args = ap.parse_args()

    source, candidates = load_candidates(args.input)
    if args.candidate_index is not None:
        candidates = [candidates[args.candidate_index]]

    results = []
    failed_expectations = []
    for i, candidate in enumerate(candidates):
        result = certify_candidate(candidate, args.precision_bits)
        results.append(result)
        expected = bool(candidate.get("expect_fb04_scoped_counterexample", False))
        if expected and not result["fb04_scoped_counterexample_certified"]:
            failed_expectations.append(i)

    certified_counterexamples = [r for r in results if r["fb04_scoped_counterexample_certified"]]
    payload = {
        "schema_version": "POST150_SELECTED_RESIDUAL_CERTIFICATE_v1",
        "status": "FAIL" if failed_expectations else "PASS",
        "phase": "RIGOROUS_FINITE_NUMERICAL_AUDIT",
        "input_schema": source.get("schema_version"),
        "precision_bits": args.precision_bits,
        "candidate_count": len(results),
        "certified_fb04_scoped_counterexample_count": len(certified_counterexamples),
        "fb04_status": (
            "H3_SCOPED_SIGN_MECHANISM_FALSIFIED_BY_CERTIFIED_FINITE_STATE"
            if certified_counterexamples
            else "OPEN_NO_CHECKED_IN_CERTIFIED_COUNTEREXAMPLE"
        ),
        "results": results,
        "claim_firewall": {
            "theorem_authority": False,
            "terminal_claim": "RH_OPEN",
            "whole_cell_ancestry": "NOT_CERTIFIED_BY_THIS_TOOL",
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": payload["status"],
                "candidate_count": payload["candidate_count"],
                "certified_fb04_scoped_counterexample_count": payload["certified_fb04_scoped_counterexample_count"],
                "fb04_status": payload["fb04_status"],
            },
            indent=2,
        )
    )
    return 1 if failed_expectations else 0


if __name__ == "__main__":
    raise SystemExit(main())
