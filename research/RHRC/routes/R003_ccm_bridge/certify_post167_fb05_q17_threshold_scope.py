#!/usr/bin/env python3
"""Rigorous pointwise Arb replay for the post-#167 Q16/Q17 threshold audit.

This intentionally avoids the dependency-heavy whole-cell interval strategy
falsified by PR #167.  It certifies the exact threshold continuations and a
geometric sequence of exact dyadic source-coordinate points on both sides.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, canonical_source_matrix, set_precision, to_arb_rational
from canonical_source_numeric import dyadic_inside_fixed_cell
from post150_selected_residual import exact_parity_basis
from post166_fb05_cell_interval import (
    _arb_matrix_from_sympy,
    classify_principal_minors,
    fixed_q_canonical_source_matrix_arb,
    principal_determinants_arb,
)
from post167_fb05_threshold_jet import final_sylvester_pivot_arb

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post167_fb05_q17_threshold_v1.json"


def _entrywise_overlap(A, B) -> bool:
    return A.nrows() == B.nrows() and A.ncols() == B.ncols() and all(
        (A[r, c] - B[r, c]).contains(0)
        for r in range(A.nrows())
        for c in range(A.ncols())
    )


def _point_certificate(M, K: int, parity: str) -> dict:
    B = exact_parity_basis(K, parity)
    Bb = _arb_matrix_from_sympy(B)
    H = Bb.transpose() * M * Bb
    minors = principal_determinants_arb(H)
    raw_class = classify_principal_minors(minors)
    if raw_class == "POSITIVE_CERTIFIED":
        classification = "POSITIVE_CERTIFIED"
    elif raw_class == "BAD_INTERVAL_CERTIFIED":
        classification = "NEGATIVE_WITNESS_CERTIFIED"
    else:
        classification = "UNRESOLVED"
    pivot = final_sylvester_pivot_arb(H)
    return {
        "classification": classification,
        "raw_classification": raw_class,
        "leading_principal_minors": [ball_record(x) for x in minors],
        "final_sylvester_pivot": None if pivot is None else ball_record(pivot),
    }


def _source_offset_point(q: int, K: int, parity: str, sign: int, exponent: int) -> dict:
    den = 1 << exponent
    omega = to_arb_rational(sign, den)
    L = arb(q).log() / (1 - omega)
    Q = q - 1 if sign < 0 else q
    M = canonical_source_matrix(L, K, Q)
    cert = _point_certificate(M, K, parity)
    return {
        "side": "left" if sign < 0 else "right",
        "physical_Q": Q,
        "omega_num": sign,
        "omega_den": den,
        "omega": ball_record(omega),
        "L": ball_record(L),
        **cert,
    }


def _certify_discovery_candidate(discovery: dict, q: int, K: int, parity: str) -> dict | None:
    cell = discovery.get("q17_cell", {})
    if int(cell.get("negative_record_count", 0)) <= 0:
        return None
    best = cell.get("best_normalized_min_eigenvalue", {})
    t = float(best["t"])
    num, den = dyadic_inside_fixed_cell(q, t, bits=48)
    L = to_arb_rational(num, den)
    M = canonical_source_matrix(L, K, q)
    return {
        "source": "quantized floating best-negative candidate",
        "L_num": num,
        "L_den": den,
        **_point_certificate(M, K, parity),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--discovery", type=Path, default=Path("/tmp/POST167_FB05_Q17_THRESHOLD_DISCOVERY.json"))
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST167_FB05_Q17_THRESHOLD_CERTIFICATE.json"))
    ap.add_argument("--precision-bits", type=int, default=None)
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    target = fixture["target"]
    q = int(target["q"])
    N = int(target["predecessor_N"])
    K = int(target["successor_K"])
    parity = target["selected_parity"]
    if K != N + 1:
        raise AssertionError("fixture successor is not predecessor+1")
    precision = int(args.precision_bits or fixture.get("arb_precision_bits", 256))
    set_precision(precision)

    # Exact threshold: Q=q-1 and Q=q fixed-cutoff continuations must agree
    # because the entering q atom vanishes at omega=0.
    L0 = arb(q).log()
    left_M = fixed_q_canonical_source_matrix_arb(L0, K, q - 1)
    right_M = fixed_q_canonical_source_matrix_arb(L0, K, q)
    threshold_overlap = _entrywise_overlap(left_M, right_M)
    if not threshold_overlap:
        raise AssertionError("left/right fixed-cutoff threshold continuations do not overlap")
    threshold_cert = _point_certificate(left_M, K, parity)

    microscope = []
    for sign in (-1, 1):
        for exponent in fixture["source_offset_exponents"]:
            microscope.append(_source_offset_point(q, K, parity, sign, int(exponent)))

    discovery = json.loads(args.discovery.read_text(encoding="utf-8")) if args.discovery.exists() else {}
    replay = _certify_discovery_candidate(discovery, q, K, parity) if discovery else None

    counts = {"POSITIVE_CERTIFIED": 0, "NEGATIVE_WITNESS_CERTIFIED": 0, "UNRESOLVED": 0}
    for rec in microscope:
        counts[rec["classification"]] += 1
    if replay is not None:
        counts[replay["classification"]] += 1

    out = {
        "schema_version": "POST167_FB05_Q17_THRESHOLD_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_POINT_CERTIFICATION_ONLY",
        "target": target,
        "precision_bits": precision,
        "threshold": {
            "L": ball_record(L0),
            "left_Q": q - 1,
            "right_Q": q,
            "continuations_overlap_entrywise": threshold_overlap,
            **threshold_cert,
        },
        "microscope": microscope,
        "discovery_candidate_replay": replay,
        "classification_counts": counts,
        "interpretation": (
            "Only exact finite threshold/source-coordinate points are certified. "
            "A certified negative point is valuable finite evidence and does not make CI fail."
        ),
        "nonclaims": [
            "Finite point certification is not a whole-cell theorem.",
            "No threshold point result is Lean theorem authority.",
            "A finite bad successor is not itself an RH contradiction.",
            "RH remains OPEN.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "target": target,
        "threshold_classification": threshold_cert["classification"],
        "threshold_continuations_overlap": threshold_overlap,
        "classification_counts": counts,
        "discovery_candidate_replay": replay,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
