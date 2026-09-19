#!/usr/bin/env python3
"""Rigorous finite certifier for the post-#222 bi-regular zero-shift scalar.

The scope ladder is intentionally strict:

BIREGULAR_POINT
  both zero-shift predecessor blocks are rigorously positive definite;

BIREGULAR_H3_ALIGNED
  plus selected-even sigma<0 and every smaller size is positive at the same L;

CELL_MINIMAL_BIREGULAR_ALIGNED
  plus size K=2 is positive in both parities over the entire cutoff cell.

Only the final class is allowed to inform the exact retained post-#222 scalar
route.  Every scalar-sign outcome is a legitimate PASS result.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import set_precision
from certify_post150_selected_residual_scope import certify_smaller_sizes
from post166_fb05_cell_interval import adaptive_cell_cover, cell_coordinate_L_arb
from post222_fb05_biregular_zero_shift_scalar import (
    biregular_zero_shift_scalar_record_arb,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post222_fb05_biregular_zero_shift_scalar_v1.json"


def _whole_cell_ancestry(Q: int, fx: dict) -> dict:
    wc = fx["whole_cell_ancestry"]
    pred_N = int(wc["predecessor_N_for_cover"])
    max_depth = int(wc["max_depth"])
    covers = {
        parity: adaptive_cell_cover(Q, pred_N, parity, max_depth=max_depth)
        for parity in wc["parities"]
    }
    certified = all(c["whole_cell_positive_certified"] for c in covers.values())
    return {
        "Q": Q,
        "smaller_successor_K": int(wc["smaller_successor_K"]),
        "covers": covers,
        "certified": certified,
        "meaning": (
            "For K*=3, K=0 and K=1 parity carriers are zero-dimensional. "
            "Whole-cell positivity of K=2 in both parities therefore certifies "
            "the complete smaller-size CellAnyParityBad ancestry required by "
            "the retained cell-minimal certificate."
        ),
    }


def _point_scope(point: dict, fx: dict, whole_cell: dict) -> dict:
    Q = int(point["Q"])
    t_num = int(point["t_num"])
    t_den = int(point["t_den"])
    N = int(fx["selected_target"]["predecessor_N"])

    rec = biregular_zero_shift_scalar_record_arb(Q, t_num, t_den, N=N)
    t = arb(t_num) / t_den
    L = cell_coordinate_L_arb(Q, t)
    same_aperture = certify_smaller_sizes(Q, L, N)

    biregular = (
        rec["even"]["predecessor_pd"]["certified"]
        and rec["odd"]["predecessor_pd"]["certified"]
    )
    selected_even_bad = bool(rec["sigma_plus_negative_certified"])
    h3 = biregular and selected_even_bad and bool(same_aperture["certified"])
    cell_minimal = h3 and bool(whole_cell["certified"])

    if cell_minimal:
        scope = "CELL_MINIMAL_BIREGULAR_ALIGNED"
    elif h3:
        scope = "BIREGULAR_H3_ALIGNED"
    elif biregular:
        scope = "BIREGULAR_POINT"
    else:
        scope = "NOT_BIREGULAR"

    return {
        "label": point["label"],
        "Q": Q,
        "t_num": t_num,
        "t_den": t_den,
        "zero_shift": rec,
        "same_aperture_smaller_size_ancestry": same_aperture,
        "whole_cell_smaller_size_ancestry": whole_cell,
        "scope": {
            "biregular": biregular,
            "selected_even_bad": selected_even_bad,
            "same_aperture_H3": h3,
            "cell_minimal": cell_minimal,
            "classification": scope,
        },
        "retained_scalar_classification": (
            rec["sigma_minus_classification"]
            if cell_minimal
            else "NOT_CELL_MINIMAL_RETAINED_SCOPE"
        ),
    }


def _overall(rows: list[dict]) -> str:
    qualified = [
        r for r in rows
        if r["scope"]["classification"] == "CELL_MINIMAL_BIREGULAR_ALIGNED"
    ]
    if not qualified:
        return "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED"

    classes = {r["retained_scalar_classification"] for r in qualified}
    neg = "SIGMA_MINUS_NEGATIVE_CERTIFIED" in classes
    pos = "SIGMA_MINUS_POSITIVE_CERTIFIED" in classes
    unr = "SIGMA_MINUS_SIGN_UNRESOLVED" in classes

    if neg and (pos or unr):
        return "BIREGULAR_RETAINED_SCALAR_SIGN_MIXED_ON_QUALIFIED_SCOPE"
    if neg:
        return "BIREGULAR_RETAINED_SCALAR_NEGATIVE_WITNESS_CERTIFIED"
    if unr:
        return "BIREGULAR_RETAINED_SCALAR_SIGN_UNRESOLVED"
    if pos:
        return "BIREGULAR_RETAINED_SCALAR_POSITIVE_ON_QUALIFIED_FROZEN_SCOPE"
    raise AssertionError("unknown retained scalar classification set")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST222_BIREGULAR_ZERO_SHIFT_SCALAR_CERTIFICATE.json"))
    args = ap.parse_args()

    fx = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    set_precision(int(fx["arb_precision_bits"]))

    qs = sorted({int(p["Q"]) for p in schedule["points"]})
    whole_cells = {Q: _whole_cell_ancestry(Q, fx) for Q in qs}
    rows = [_point_scope(p, fx, whole_cells[int(p["Q"])]) for p in schedule["points"]]
    overall = _overall(rows)

    out = {
        "schema_version": "POST222_FB05_BIREGULAR_ZERO_SHIFT_SCALAR_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fx["claim_cap"],
        "theorem_authority_pr": fx["theorem_authority_pr"],
        "latest_research_authority_pr": fx["latest_research_authority_pr"],
        "precision_bits": int(fx["arb_precision_bits"]),
        "overall_classification": overall,
        "qualified_cell_minimal_point_count": sum(
            r["scope"]["classification"] == "CELL_MINIMAL_BIREGULAR_ALIGNED"
            for r in rows
        ),
        "whole_cell_ancestry": whole_cells,
        "points": rows,
        "theorem_promotion": False,
        "obs_059i_closed": False,
        "simultaneous_odd_bad_excluded": False,
        "negative_root_exclusion": False,
        "finite_to_infinite_closure": False,
        "rh_claim": False,
        "nonclaims": [
            "This certificate is rigorous finite Arb research evidence, not Lean theorem authority.",
            "A same-aperture H3 point is not promoted to retained cell-minimal scope without whole-cell K=2 positivity in both parities.",
            "A negative qualified sigma_minus falsifies only the audited finite retained-scalar positivity candidate.",
            "A positive qualified frozen sample does not prove arbitrary-Q positivity.",
            "OBS-059I remains OPEN.",
            "No negative-root exclusion, finite-to-infinite closure, FB-05 closure, or RH theorem is established.",
            "RH remains OPEN."
        ],
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "overall_classification": overall,
        "qualified_cell_minimal_point_count": out["qualified_cell_minimal_point_count"],
        "point_scopes": [
            {
                "label": r["label"],
                "scope": r["scope"]["classification"],
                "sigma_minus": r["retained_scalar_classification"],
            }
            for r in rows
        ],
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
