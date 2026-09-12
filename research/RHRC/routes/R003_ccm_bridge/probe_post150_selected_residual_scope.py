#!/usr/bin/env python3
"""Broad floating-point scout for the post-#150 selected-residual sign.

This executable intentionally separates discovery from certification. It uses
exact rational carrier/shell geometry but ordinary floating-point production
source matrices. Any candidate it emits must be replayed by
``certify_post150_selected_residual_scope.py`` before it can count toward
E4A4-SCHUR-FB-04.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from canonical_source_numeric import dyadic_inside_fixed_cell
from post150_selected_residual import (
    evaluate_selected_residual_state,
    same_aperture_smaller_size_goodness,
)

SCOPE_RANK = {"NONE": 0, "H0": 1, "H1": 2, "H2": 3, "H3": 4}


def sampled_cell_ancestry_heuristic(
    Q: int,
    N: int,
    sample_points: list[tuple[int, int]],
    tol: float,
) -> dict:
    rows = []
    survives = True
    for num, den in sample_points:
        L = num / den
        result = same_aperture_smaller_size_goodness(L, N, Q, tol=tol)
        rows.append(
            {
                "L_num": num,
                "L_den": den,
                "L": L,
                "all_smaller_good": result["all_good"],
            }
        )
        survives = survives and result["all_good"]
    return {
        "status": "CELL_ANCESTRY_DISCOVERY_HEURISTIC",
        "all_sampled_apertures_smaller_good": survives,
        "rows": rows,
        "nonclaim": (
            "Finite sampling does not establish whole-cell minimal ancestry "
            "from the #150 construction."
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q-min", type=int, default=2)
    ap.add_argument("--q-max", type=int, default=12)
    ap.add_argument("--n-min", type=int, default=1)
    ap.add_argument("--n-max", type=int, default=8)
    ap.add_argument("--samples", type=int, default=5)
    ap.add_argument("--dyadic-bits", type=int, default=40)
    ap.add_argument("--tol", type=float, default=2e-9)
    ap.add_argument("--top", type=int, default=30)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST150_SELECTED_RESIDUAL_DISCOVERY.json"),
    )
    args = ap.parse_args()

    if args.q_min < 1 or args.q_max < args.q_min:
        raise SystemExit("invalid Q range")
    if args.n_min < 1 or args.n_max < args.n_min:
        raise SystemExit("invalid N range")
    if args.samples < 1:
        raise SystemExit("samples must be positive")

    scanned = 0
    negatives = []
    scope_counts = {k: 0 for k in SCOPE_RANK}
    per_cell_points: dict[int, list[tuple[int, int]]] = {}

    for Q in range(args.q_min, args.q_max + 1):
        points = [
            dyadic_inside_fixed_cell(
                Q,
                (j + 1) / (args.samples + 1),
                bits=args.dyadic_bits,
            )
            for j in range(args.samples)
        ]
        per_cell_points[Q] = points
        for num, den in points:
            L = num / den
            for N in range(args.n_min, args.n_max + 1):
                for parity in ("even", "odd"):
                    state = evaluate_selected_residual_state(Q, L, N, parity, tol=args.tol)
                    scanned += 1
                    scope_counts[state["scope"]["highest"]] += 1
                    if state["selected_residual"]["negative_signal"]:
                        state["L_num"] = num
                        state["L_den"] = den
                        negatives.append(state)

    negatives.sort(
        key=lambda row: (
            -SCOPE_RANK[row["scope"]["highest"]],
            row["selected_residual"]["direct_trial_energy"],
        )
    )
    selected = negatives[: args.top]

    for row in selected:
        if row["scope"]["H3_all_smaller_sizes_both_parities_good_same_aperture"]:
            row["sampled_cell_ancestry"] = sampled_cell_ancestry_heuristic(
                row["Q"], row["N"], per_cell_points[row["Q"]], args.tol
            )

    payload = {
        "schema_version": "POST150_SELECTED_RESIDUAL_DISCOVERY_v1",
        "status": "PASS",
        "phase": "DISCOVERY_AUDIT",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "configuration": {
            "q_min": args.q_min,
            "q_max": args.q_max,
            "n_min": args.n_min,
            "n_max": args.n_max,
            "samples_per_cell": args.samples,
            "dyadic_bits": args.dyadic_bits,
            "tolerance": args.tol,
        },
        "scanned_states": scanned,
        "scope_counts": scope_counts,
        "negative_selected_residual_count": len(negatives),
        "top_negative_candidates": selected,
        "certification_instruction": (
            "Copy a candidate into the checked-in fixture or pass it to "
            "certify_post150_selected_residual_scope.py. Floating precision "
            "alone does not close E4A4-SCHUR-FB-04."
        ),
        "nonclaims": [
            "No floating result is theorem authority.",
            "No sampled-cell statement proves whole-cell #150 ancestry.",
            "An arbitrary nonzero shell generator preserves sign but not the canonical cubic magnitude.",
            "RH remains OPEN.",
        ],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": payload["status"],
                "scanned_states": scanned,
                "scope_counts": scope_counts,
                "negative_selected_residual_count": len(negatives),
                "top": [
                    {
                        "Q": x["Q"],
                        "L_num": x["L_num"],
                        "L_den": x["L_den"],
                        "N": x["N"],
                        "parity": x["parity"],
                        "scope": x["scope"]["highest"],
                        "energy": x["selected_residual"]["direct_trial_energy"],
                    }
                    for x in selected[:10]
                ],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
