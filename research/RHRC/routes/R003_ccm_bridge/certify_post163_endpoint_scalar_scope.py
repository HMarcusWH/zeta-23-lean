#!/usr/bin/env python3
"""Rigorous Arb replay for post-#163 endpoint-scalar audit fixtures.

This certifies only declared finite points.  It does not establish a global
sign theorem and has no Lean/RH promotion authority.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from canonical_riesz_endpoint_scalar import endpoint_record_arb

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post163_endpoint_scalar_v1.json"


def load_candidates(path: Path) -> tuple[dict, list[dict]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if "candidates" not in payload:
        raise ValueError("fixture must contain candidates")
    return payload, list(payload["candidates"])


def certify_candidate(candidate: dict, precision_bits: int) -> dict:
    Q = int(candidate["Q"])
    num = int(candidate["L_num"])
    den = int(candidate["L_den"])
    r = int(candidate.get("riesz_order", 8))
    rec = endpoint_record_arb(r, Q, num, den, precision_bits=precision_bits)
    rec["selection"] = candidate.get("selection")
    rec["certified_finite_point"] = bool(rec["cell"]["certified"])
    rec["claim_cap"] = "RIGOROUS_FINITE_POINT_CERTIFICATION_ONLY"
    rec["nonclaims"] = [
        "This enclosure certifies only the declared aperture.",
        "No finite collection of enclosures proves global endpoint-scalar positivity.",
        "No numerical result is Lean theorem authority.",
        "No FB-05 closure or RH claim follows.",
        "RH remains OPEN.",
    ]
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST163_ENDPOINT_SCALAR_CERTIFICATE.json"),
    )
    ap.add_argument("--precision-bits", type=int, default=320)
    ap.add_argument("--candidate-index", type=int, default=None)
    args = ap.parse_args()

    if args.precision_bits < 128:
        raise SystemExit("precision-bits must be at least 128")

    fixture, candidates = load_candidates(args.input)
    if args.candidate_index is not None:
        if not 0 <= args.candidate_index < len(candidates):
            raise SystemExit("candidate-index out of range")
        candidates = [candidates[args.candidate_index]]

    results = [certify_candidate(c, args.precision_bits) for c in candidates]
    invalid = [r for r in results if not r["certified_finite_point"]]

    counts = {"POSITIVE": 0, "NEGATIVE": 0, "CONTAINS_ZERO": 0}
    for row in results:
        counts[row["sign_classification"]] += 1

    payload = {
        "schema_version": "POST163_ENDPOINT_SCALAR_CERTIFICATE_v1",
        "status": "PASS" if not invalid else "FAIL",
        "phase": "RIGOROUS_FINITE_REPLAY",
        "claim_cap": "RIGOROUS_FINITE_POINT_CERTIFICATION_ONLY",
        "fixture_schema_version": fixture.get("schema_version"),
        "precision_bits": args.precision_bits,
        "candidate_count": len(results),
        "sign_counts": counts,
        "results": results,
        "invalid_candidates": invalid,
        "nonclaims": [
            "The sign_counts field is a finite-fixture summary, not a global sign theorem.",
            "CONTAINS_ZERO means the requested enclosure did not separate zero at this precision.",
            "No finite numerical audit is theorem authority.",
            "RH remains OPEN.",
        ],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": payload["status"],
                "candidate_count": payload["candidate_count"],
                "sign_counts": counts,
                "output": str(args.output),
            },
            indent=2,
        )
    )
    return 0 if not invalid else 1


if __name__ == "__main__":
    raise SystemExit(main())
