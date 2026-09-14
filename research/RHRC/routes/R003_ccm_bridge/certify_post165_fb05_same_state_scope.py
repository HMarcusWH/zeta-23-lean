#!/usr/bin/env python3
"""Rigorous finite replay for post-#165 FB-05 same-state candidates.

The floating scout proposes a negative secular root and rational witnesses.  The
certificate independently rebuilds the production canonical source with Arb,
certifies a rational sign bracket for the root, solves the interval shifted
system H-lambda G, and encloses the even M4/source-moment observables on that
root bracket.  Floating values select candidates only; every advertised
certificate is decided by Arb balls.

This is finite numerical certification, not Lean theorem authority.  It cannot
promote an RH claim.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp
from flint import arb, arb_mat

from canonical_riesz_endpoint_scalar import (
    canonical_riesz_endpoint_scalar_arb,
    sign_classification_arb,
)
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
from certify_post150_selected_residual_scope import (
    certify_candidate as certify_post150_candidate,
    positive_definite_certificate,
)
from post150_selected_residual import (
    centered_predecessor_basis,
    exact_parity_basis,
    exact_shell_generator,
)
from post165_fb05_shifted_state import (
    evaluate_shifted_state,
    shifted_predecessor_system,
    shifted_secular_scalar,
)
from canonical_source_numeric import canonical_source_matrix_L

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post165_fb05_same_state_v1.json"


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


def _restriction(M: arb_mat, B: sp.Matrix) -> arb_mat:
    if B.cols == 0:
        return arb_mat(0, 0)
    X = _arb_matrix_from_sympy(B)
    return X.transpose() * M * X


def _vector_overlap_zero(v: arb_mat) -> bool:
    return all(v[r, c].contains(0) for r in range(v.nrows()) for c in range(v.ncols()))


def _secular_arb(lam: arb, H: arb_mat, G: arb_mat, r: arb_mat, q: arb, c2: arb) -> arb:
    if H.nrows() == 0:
        return q - lam * c2
    x = (H - G * lam).solve(r)
    return q - lam * c2 - _scalar(r.transpose() * x)


def _dyadic_root_bracket(float_rec: dict, bits: int = 44) -> tuple[int, int, int]:
    """Propose an exact dyadic bracket; Arb will decide whether it is valid."""
    lam = float(float_rec["secular"]["lambda"])
    if not lam < 0:
        raise ValueError("floating root proposal is not negative")
    Q = int(float_rec["Q"])
    L = float(float_rec["L"])
    N = int(float_rec["N"])
    parity = float_rec["parity"]
    M = canonical_source_matrix_L(L, N + 1)
    W = centered_predecessor_basis(N, parity)
    c = exact_shell_generator(N, parity)
    H, G, r, q, c2 = shifted_predecessor_system(M, W, c)

    den = 1 << int(bits)
    center = int(round(lam * den))
    radius = 2
    for _ in range(50):
        lo_num = center - radius
        hi_num = center + radius
        if hi_num >= 0:
            hi_num = -1
        lo = lo_num / den
        hi = hi_num / den
        if not lo < hi < 0:
            radius *= 2
            continue
        try:
            flo = shifted_secular_scalar(lo, H, G, r, q, c2)
            fhi = shifted_secular_scalar(hi, H, G, r, q, c2)
        except Exception:
            radius *= 2
            continue
        if flo > 0 and fhi < 0:
            return lo_num, hi_num, den
        radius *= 2
    raise ArithmeticError("failed to propose dyadic root bracket")


def _quadratic_normal_column(K: int) -> arb_mat:
    d = list(range(-K, K + 1))
    dim = len(d)
    sum2 = sum(x * x for x in d)
    values = []
    for x in d:
        num = dim * x * x - sum2
        values.append(to_arb_rational(num, dim))
    return arb_mat([[x] for x in values])


def _centered_moment_ball(u: arb_mat, K: int, order: int) -> arb:
    total = arb(0)
    for row, d in enumerate(range(-K, K + 1)):
        total += (d ** int(order)) * u[row, 0]
    return total


def _source_moment_ball(M: arb_mat, u: arb_mat, K: int) -> arb:
    n2 = _quadratic_normal_column(K)
    den = _scalar(n2.transpose() * n2)
    return _scalar(n2.transpose() * M * u) / den


def _source_channel_record(Q: int, L: arb, K: int, u: arb_mat, direct: arb) -> dict:
    n2 = _quadratic_normal_column(K)
    den = _scalar(n2.transpose() * n2)
    channels = signed_channel_matrices(L, K, Q)
    records = {}
    total = arb(0)
    scalar_value = None
    for name, A in channels.items():
        value = _scalar(n2.transpose() * A * u) / den
        records[name] = ball_record(value)
        total += value
        if name == "scalar_shift":
            scalar_value = value
    delta = total - direct
    return {
        "signed_channels": records,
        "sum": ball_record(total),
        "direct": ball_record(direct),
        "reconstruction_difference": ball_record(delta),
        "reconstruction_overlap": bool(delta.contains(0)),
        "scalar_shift_contains_zero": bool(scalar_value is not None and scalar_value.contains(0)),
    }


def _opposite_parity_certificate(
    M: arb_mat,
    K: int,
    selected_parity: str,
    float_rec: dict,
) -> dict:
    parity = "odd" if selected_parity == "even" else "even"
    V = exact_parity_basis(K, parity)
    H = _restriction(M, V)
    pd = positive_definite_certificate(H)
    witness = float_rec["opposite_parity"].get("bad_witness_coeffs_in_exact_successor_basis")
    bad = None
    if witness is not None and len(witness) == V.cols:
        y = _column([int(x) for x in witness])
        qbad = _quadratic(H, y)
        bad = {
            "certified": definitely_negative(qbad),
            "witness_coeffs": [int(x) for x in witness],
            "quadratic_value": ball_record(qbad),
        }
    if pd["certified"]:
        classification = "GOOD_CERTIFIED"
    elif bad is not None and bad["certified"]:
        classification = "BAD_CERTIFIED"
    else:
        classification = "UNRESOLVED"
    return {
        "parity": parity,
        "classification": classification,
        "positive_definite": pd,
        "negative_witness": bad,
    }


def certify_case(candidate: dict, precision_bits: int) -> dict:
    set_precision(precision_bits)
    Q = int(candidate["Q"])
    N = int(candidate["N"])
    K = N + 1
    parity = candidate["parity"]
    num = int(candidate["L_num"])
    den = int(candidate["L_den"])
    L = to_arb_rational(num, den)
    cell = fixed_cell_membership(Q, L)

    float_rec = evaluate_shifted_state(Q, num / den, N, parity)
    selected_witness = None
    if float_rec.get("available"):
        selected_witness = float_rec.get("selected_bad_witness_coeffs_in_exact_successor_basis")
    post150_input = dict(candidate)
    if selected_witness is not None:
        post150_input["bad_witness_coeffs_in_exact_successor_basis"] = selected_witness
    post150 = certify_post150_candidate(post150_input, precision_bits)

    base = {
        "candidate": {
            "Q": Q,
            "L_num": num,
            "L_den": den,
            "N": N,
            "Kstar": K,
            "parity": parity,
            "purpose": candidate.get("purpose"),
        },
        "precision_bits": precision_bits,
        "cell": cell,
        "post150_scope": post150.get("scope"),
        "post150_replay": post150,
        "floating_discovery_available": bool(float_rec.get("available")),
        "claim_cap": "RIGOROUS_FINITE_INTERVAL_EVIDENCE_ONLY",
    }
    if not cell["certified"]:
        base.update({"certified": False, "shifted_root_certified": False, "failure": "cell_not_certified"})
        return base
    if not float_rec.get("available"):
        base.update(
            {
                "certified": True,
                "shifted_root_certified": False,
                "failure": float_rec.get("failure", "no_shifted_state_discovered"),
                "nonclaims": ["No negative shifted state was promoted from this fixture.", "RH remains OPEN."],
            }
        )
        return base

    W = centered_predecessor_basis(N, parity)
    c = exact_shell_generator(N, parity)
    Wb = _arb_matrix_from_sympy(W)
    cb = _arb_matrix_from_sympy(c)
    M = canonical_source_matrix(L, K, Q)
    H = Wb.transpose() * M * Wb if W.cols else arb_mat(0, 0)
    G = Wb.transpose() * Wb if W.cols else arb_mat(0, 0)
    r = Wb.transpose() * M * cb if W.cols else arb_mat(0, 1)
    q = _quadratic(M, cb)
    c2 = _scalar(cb.transpose() * cb)

    lo_num, hi_num, lam_den = _dyadic_root_bracket(float_rec)
    lo = to_arb_rational(lo_num, lam_den)
    hi = to_arb_rational(hi_num, lam_den)
    flo = _secular_arb(lo, H, G, r, q, c2)
    fhi = _secular_arb(hi, H, G, r, q, c2)
    bracket_certified = definitely_positive(flo) and definitely_negative(fhi) and hi_num < 0

    mid_num = lo_num + hi_num
    mid_den = 2 * lam_den
    rad_num = hi_num - lo_num
    rad_den = 2 * lam_den
    lam_ball = arb(f"{mid_num}/{mid_den}", f"{rad_num}/{rad_den}")

    trial_failure = None
    try:
        if W.cols:
            x = (H - G * lam_ball).solve(r)
            u = cb - Wb * x
        else:
            u = cb
        residual = M * u - u * lam_ball
        pred_residual = Wb.transpose() * residual if W.cols else arb_mat(0, 1)
        pred_overlap = _vector_overlap_zero(pred_residual)
        shell_residual = _scalar(cb.transpose() * residual)
        shell_zero_possible = bool(shell_residual.contains(0))
    except Exception as exc:
        trial_failure = repr(exc)
        u = None
        pred_overlap = False
        shell_residual = None
        shell_zero_possible = False

    m4 = None
    source = None
    channels = None
    if u is not None and parity == "even":
        m4 = _centered_moment_ball(u, K, 4)
        source = _source_moment_ball(M, u, K)
        channels = _source_channel_record(Q, L, K, u, source)

    opposite = _opposite_parity_certificate(M, K, parity, float_rec)
    s8 = canonical_riesz_endpoint_scalar_arb(8, Q, L)

    shifted_root_certified = bool(bracket_certified and pred_overlap and shell_zero_possible)
    result = {
        **base,
        "root_bracket": {
            "lambda_lo_num": lo_num,
            "lambda_hi_num": hi_num,
            "lambda_den": lam_den,
            "f_lo": ball_record(flo),
            "f_hi": ball_record(fhi),
            "certified": bracket_certified,
            "interval": ball_record(lam_ball),
        },
        "shifted_trial": {
            "constructed": u is not None,
            "failure": trial_failure,
            "predecessor_residual_contains_zero_entrywise": pred_overlap,
            "shell_residual": ball_record(shell_residual) if shell_residual is not None else None,
            "shell_residual_contains_zero": shell_zero_possible,
        },
        "shifted_root_certified": shifted_root_certified,
        "even_observables": (
            {
                "M4": ball_record(m4),
                "M4_nonzero_certified": definitely_nonzero(m4),
                "explicitCanonicalSourceMoment": ball_record(source),
                "source_moment_nonzero_certified": definitely_nonzero(source),
                "source_channels": channels,
            }
            if parity == "even" and m4 is not None and source is not None
            else None
        ),
        "opposite_parity": opposite,
        "endpoint_scalar": {
            "S8": ball_record(s8),
            "sign_classification": sign_classification_arb(s8),
            "nonzero_certified": definitely_nonzero(s8),
        },
        "nonclaims": [
            "This is a finite Arb enclosure, not Lean theorem authority.",
            "A certified root bracket does not prove a whole-cell statement.",
            "No global sourceMoment/M4 implication follows from sampled states.",
            "No global endpoint-scalar sign theorem follows from sampled states.",
            "RH remains OPEN.",
        ],
    }
    result["certified"] = bool(
        cell["certified"]
        and shifted_root_certified
        and (channels is None or channels["reconstruction_overlap"])
    )
    return result


def load_cases(path: Path) -> tuple[dict, list[dict]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("candidates"):
        return payload, list(payload["candidates"])
    if payload.get("smoke_cases"):
        return payload, list(payload["smoke_cases"])
    raise ValueError("fixture contains neither candidates nor smoke_cases")


def _expectation_failures(candidate: dict, result: dict) -> list[str]:
    failures = []
    if candidate.get("expect_shifted_root") is True and not result.get("shifted_root_certified"):
        failures.append("expected shifted root was not certified")
    if candidate.get("expect_h3") is True:
        scope = result.get("post150_scope") or {}
        if not scope.get("H3_all_smaller_sizes_both_parities_good_same_aperture"):
            failures.append("expected H3 scope was not certified")
    expected_opp = candidate.get("expect_opposite_classification")
    if expected_opp and result.get("opposite_parity", {}).get("classification") != expected_opp:
        failures.append(f"expected opposite parity {expected_opp}")
    expected_s8 = candidate.get("expect_s8_sign")
    if expected_s8 and result.get("endpoint_scalar", {}).get("sign_classification") != expected_s8:
        failures.append(f"expected S8 sign {expected_s8}")
    if candidate.get("expect_source_moment_nonzero") is True:
        obs = result.get("even_observables") or {}
        if not obs.get("source_moment_nonzero_certified"):
            failures.append("expected source moment nonzero was not certified")
    if candidate.get("expect_m4_nonzero") is True:
        obs = result.get("even_observables") or {}
        if not obs.get("M4_nonzero_certified"):
            failures.append("expected M4 nonzero was not certified")
    return failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST165_FB05_SAME_STATE_CERTIFICATE.json"),
    )
    ap.add_argument("--precision-bits", type=int, default=256)
    args = ap.parse_args()

    source, candidates = load_cases(args.input)
    results = []
    failures = []
    for i, candidate in enumerate(candidates):
        result = certify_case(candidate, args.precision_bits)
        result["expectation_failures"] = _expectation_failures(candidate, result)
        if result["expectation_failures"]:
            failures.append({"index": i, "failures": result["expectation_failures"]})
        results.append(result)

    payload = {
        "schema_version": "POST165_FB05_SAME_STATE_CERTIFICATE_v1",
        "status": "FAIL" if failures else "PASS",
        "phase": "RIGOROUS_FINITE_INTERVAL_AUDIT",
        "input_schema": source.get("schema_version"),
        "precision_bits": args.precision_bits,
        "candidate_count": len(results),
        "certified_shifted_root_count": sum(bool(r.get("shifted_root_certified")) for r in results),
        "expectation_failures": failures,
        "results": results,
        "claim_firewall": {
            "theorem_authority": False,
            "terminal_claim": "RH_OPEN",
            "whole_cell_statement": "NOT_CERTIFIED_BY_THIS_TOOL",
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": payload["status"],
                "candidate_count": payload["candidate_count"],
                "certified_shifted_root_count": payload["certified_shifted_root_count"],
                "expectation_failures": failures,
                "summaries": [
                    {
                        "candidate": r["candidate"],
                        "shifted_root_certified": r.get("shifted_root_certified"),
                        "opposite_parity": r.get("opposite_parity", {}).get("classification"),
                        "S8": r.get("endpoint_scalar", {}).get("sign_classification"),
                        "M4_nonzero": (r.get("even_observables") or {}).get("M4_nonzero_certified"),
                        "source_moment_nonzero": (r.get("even_observables") or {}).get(
                            "source_moment_nonzero_certified"
                        ),
                    }
                    for r in results
                ],
            },
            indent=2,
        )
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
