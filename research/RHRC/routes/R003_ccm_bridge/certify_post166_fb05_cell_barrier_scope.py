#!/usr/bin/env python3
"""Rigorous adaptive interval audit for the post-#166 Q=16 determinant barrier.

The certifier covers the normalized cell coordinate t in [0,1] with dyadic Arb
intervals.  Each leaf is classified by Sylvester leading principal minors as
POSITIVE_CERTIFIED, BAD_INTERVAL_CERTIFIED, or UNRESOLVED.  Unresolved interval
dependency is preserved as uncertainty and never upgraded to a sign claim.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from canonical_source_arb import canonical_source_matrix, set_precision, to_arb_rational
from post150_selected_residual import exact_parity_basis
from post166_fb05_cell_interval import (
    _arb_matrix_from_sympy,
    adaptive_cell_cover,
    classify_principal_minors,
    principal_determinants_arb,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post166_fb05_cell_barrier_v1.json"


def certify_seed_point(target: dict, seed: dict) -> dict:
    Q = int(target["Q"])
    N = int(target["N"])
    K = N + 1
    parity = target["parity"]
    num = int(seed["L_num"])
    den = int(seed["L_den"])
    L = to_arb_rational(num, den)
    M = canonical_source_matrix(L, K, Q)
    B = exact_parity_basis(K, parity)
    Bb = _arb_matrix_from_sympy(B)
    H = Bb.transpose() * M * Bb
    minors = principal_determinants_arb(H)
    return {
        "L_num": num,
        "L_den": den,
        "classification": classify_principal_minors(minors),
        "leading_principal_minors": [
            {
                "ball": x.str(30, more=True),
                "contains_zero": bool(x.contains(0)),
                "positive": bool(x > 0),
                "negative": bool(x < 0),
            }
            for x in minors
        ],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST166_FB05_CELL_BARRIER_CERTIFICATE.json"))
    ap.add_argument("--precision-bits", type=int, default=192)
    ap.add_argument("--max-depth", type=int, default=None)
    args = ap.parse_args()

    payload_in = json.loads(args.input.read_text(encoding="utf-8"))
    target = payload_in["target"]
    seed = payload_in["near_critical_seed"]
    max_depth = int(args.max_depth if args.max_depth is not None else payload_in.get("max_depth", 4))
    set_precision(args.precision_bits)

    seed_cert = certify_seed_point(target, seed)
    if seed_cert["classification"] != "POSITIVE_CERTIFIED":
        raise AssertionError("checked-in #166 near-critical seed is no longer rigorously positive")

    cover = adaptive_cell_cover(
        int(target["Q"]),
        int(target["N"]),
        target["parity"],
        max_depth=max_depth,
    )
    classified_fraction = (
        float(cover["coverage_fraction"]["POSITIVE_CERTIFIED"])
        + float(cover["coverage_fraction"]["BAD_INTERVAL_CERTIFIED"])
    )

    out = {
        "schema_version": "POST166_FB05_CELL_BARRIER_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_INTERVAL_AUDIT_ONLY",
        "target": target,
        "precision_bits": args.precision_bits,
        "seed_certificate": seed_cert,
        "adaptive_cover": cover,
        "classified_fraction": classified_fraction,
        "interpretation": (
            "Whole-cell positivity is certified only when whole_cell_positive_certified is true. "
            "A bad interval is certified only when bad_interval_found is true. Otherwise the "
            "remaining region is explicitly UNRESOLVED."
        ),
        "nonclaims": [
            "UNRESOLVED does not mean negative.",
            "A finite-cell certificate is not Lean theorem authority.",
            "A bad finite successor is not itself an RH contradiction.",
            "RH remains OPEN.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": "PASS",
                "target": target,
                "seed_classification": seed_cert["classification"],
                "max_depth": max_depth,
                "leaf_count": cover["leaf_count"],
                "counts": cover["counts"],
                "coverage_fraction": cover["coverage_fraction"],
                "whole_cell_positive_certified": cover["whole_cell_positive_certified"],
                "bad_interval_found": cover["bad_interval_found"],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
