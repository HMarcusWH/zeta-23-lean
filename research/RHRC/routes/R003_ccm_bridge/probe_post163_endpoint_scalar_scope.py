#!/usr/bin/env python3
"""Broad discovery/falsification sweep for the post-#163 FB-05 endpoint scalar.

Sign changes and near-zero cases are research outputs, not test failures.
Any point selected for rigorous use must be replayed with
``certify_post163_endpoint_scalar_scope.py``.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
from scipy.optimize import minimize_scalar

from canonical_riesz_endpoint_scalar import (
    canonical_riesz_endpoint_scalar_mp,
    cell_bounds_mp,
    dyadic_inside_cell,
    endpoint_record_mp,
)


def evaluate_dyadic(Q: int, position: mp.mpf, bits: int) -> dict:
    num, den = dyadic_inside_cell(Q, position, bits=bits)
    L = mp.mpf(num) / den
    rec = endpoint_record_mp(8, Q, L)
    rec.update({"L_num": num, "L_den": den, "position": mp.nstr(position, 20)})
    return rec


def evaluate_float_candidate(Q: int, x: float, bits: int, kind: str) -> dict:
    lo, hi = cell_bounds_mp(Q)
    pos = (mp.mpf(str(x)) - lo) / (hi - lo)
    pos = min(mp.mpf("0.999999999999"), max(mp.mpf("0.000000000001"), pos))
    rec = evaluate_dyadic(Q, pos, bits)
    rec["candidate_kind"] = kind
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q-min", type=int, default=1)
    ap.add_argument("--q-max", type=int, default=128)
    ap.add_argument("--samples", type=int, default=9)
    ap.add_argument("--dyadic-bits", type=int, default=48)
    ap.add_argument("--precision-digits", type=int, default=80)
    ap.add_argument("--edge-fraction", type=str, default="0.001")
    ap.add_argument("--near-zero", type=str, default="1e-20")
    ap.add_argument("--top", type=int, default=40)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST163_ENDPOINT_SCALAR_DISCOVERY.json"),
    )
    args = ap.parse_args()

    if args.q_min < 1 or args.q_max < args.q_min:
        raise SystemExit("invalid Q range")
    if args.samples < 1:
        raise SystemExit("samples must be positive")
    if args.dyadic_bits < 16:
        raise SystemExit("dyadic-bits must be at least 16")

    mp.mp.dps = args.precision_digits
    edge = mp.mpf(args.edge_fraction)
    near_zero = mp.mpf(args.near_zero)
    if not (0 < edge < mp.mpf("0.5")):
        raise SystemExit("edge-fraction must lie in (0,1/2)")

    all_rows: list[dict] = []
    per_cell: list[dict] = []

    for Q in range(args.q_min, args.q_max + 1):
        positions = [edge]
        positions += [mp.mpf(j + 1) / (args.samples + 1) for j in range(args.samples)]
        positions += [1 - edge]
        unique_positions = []
        seen = set()
        for p in positions:
            key = str(p)
            if key not in seen:
                seen.add(key)
                unique_positions.append(p)

        cell_rows = []
        for pos in unique_positions:
            row = evaluate_dyadic(Q, pos, args.dyadic_bits)
            row["candidate_kind"] = "GRID"
            cell_rows.append(row)
            all_rows.append(row)

        lo, hi = cell_bounds_mp(Q)
        a = float(lo + edge * (hi - lo))
        b = float(hi - edge * (hi - lo))

        def f_scalar(x: float) -> float:
            return float(canonical_riesz_endpoint_scalar_mp(8, Q, mp.mpf(str(x))))

        opt_min = minimize_scalar(f_scalar, bounds=(a, b), method="bounded")
        min_row = evaluate_float_candidate(Q, float(opt_min.x), args.dyadic_bits, "CELL_MINIMUM")
        all_rows.append(min_row)
        cell_rows.append(min_row)

        opt_abs = minimize_scalar(lambda x: abs(f_scalar(x)), bounds=(a, b), method="bounded")
        zero_row = evaluate_float_candidate(
            Q, float(opt_abs.x), args.dyadic_bits, "CELL_NEAREST_ZERO"
        )
        all_rows.append(zero_row)
        cell_rows.append(zero_row)

        opt_max = minimize_scalar(lambda x: -f_scalar(x), bounds=(a, b), method="bounded")
        max_row = evaluate_float_candidate(Q, float(opt_max.x), args.dyadic_bits, "CELL_MAXIMUM")
        all_rows.append(max_row)
        cell_rows.append(max_row)

        vals = [mp.mpf(row["endpoint_scalar"]) for row in cell_rows]
        per_cell.append(
            {
                "Q": Q,
                "evaluated_points": len(cell_rows),
                "minimum": mp.nstr(min(vals), 30),
                "maximum": mp.nstr(max(vals), 30),
                "has_negative_signal": any(v < 0 for v in vals),
                "has_near_zero_signal": any(abs(v) <= near_zero for v in vals),
            }
        )

    for row in all_rows:
        v = mp.mpf(row["endpoint_scalar"])
        row["near_zero_signal"] = bool(abs(v) <= near_zero)

    negatives = [row for row in all_rows if mp.mpf(row["endpoint_scalar"]) < 0]
    negatives.sort(key=lambda row: mp.mpf(row["endpoint_scalar"]))
    closest = sorted(all_rows, key=lambda row: abs(mp.mpf(row["endpoint_scalar"])))
    smallest = min(all_rows, key=lambda row: mp.mpf(row["endpoint_scalar"]))
    largest = max(all_rows, key=lambda row: mp.mpf(row["endpoint_scalar"]))
    cancellation = sorted(
        all_rows,
        key=lambda row: (
            mp.inf
            if row["cancellation_ratio"] == "inf"
            else mp.mpf(row["cancellation_ratio"])
        ),
        reverse=True,
    )

    payload = {
        "schema_version": "POST163_ENDPOINT_SCALAR_DISCOVERY_v1",
        "status": "PASS",
        "phase": "DISCOVERY_FALSIFICATION",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "configuration": {
            "q_min": args.q_min,
            "q_max": args.q_max,
            "samples": args.samples,
            "dyadic_bits": args.dyadic_bits,
            "precision_digits": args.precision_digits,
            "edge_fraction": str(args.edge_fraction),
            "near_zero_threshold": str(args.near_zero),
        },
        "evaluated_points": len(all_rows),
        "positive_count": sum(mp.mpf(r["endpoint_scalar"]) > 0 for r in all_rows),
        "negative_count": len(negatives),
        "zero_count": sum(mp.mpf(r["endpoint_scalar"]) == 0 for r in all_rows),
        "near_zero_count": sum(bool(r["near_zero_signal"]) for r in all_rows),
        "smallest_endpoint_scalar": smallest,
        "largest_endpoint_scalar": largest,
        "closest_to_zero": closest[: args.top],
        "negative_candidates": negatives[: args.top],
        "largest_relative_cancellation": cancellation[: args.top],
        "per_cell": per_cell,
        "certification_instruction": (
            "Replay selected exact dyadics with certify_post163_endpoint_scalar_scope.py. "
            "Discovery signs are not theorem authority."
        ),
        "nonclaims": [
            "Absence of a sign change in a finite sweep does not prove global positivity.",
            "A discovered sign change is a falsification signal, not a Lean theorem.",
            "No sourceMoment-to-M4 implication is tested here.",
            "No FB-05 closure or RH claim follows.",
            "RH remains OPEN.",
        ],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": payload["status"],
                "evaluated_points": payload["evaluated_points"],
                "positive_count": payload["positive_count"],
                "negative_count": payload["negative_count"],
                "near_zero_count": payload["near_zero_count"],
                "smallest": {
                    "Q": smallest["Q"],
                    "L_num": smallest["L_num"],
                    "L_den": smallest["L_den"],
                    "endpoint_scalar": smallest["endpoint_scalar"],
                },
                "closest_to_zero": [
                    {
                        "Q": r["Q"],
                        "L_num": r["L_num"],
                        "L_den": r["L_den"],
                        "endpoint_scalar": r["endpoint_scalar"],
                    }
                    for r in closest[:5]
                ],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
