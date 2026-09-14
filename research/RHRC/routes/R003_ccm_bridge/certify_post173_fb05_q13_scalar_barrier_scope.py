#!/usr/bin/env python3
"""Adaptive Arb interval audit for the post-#173 q13/N2/even scalar barrier.

The rigorous domain is kept piecewise on physical cutoff cells Q=13,14,15.
Each interval certifies the selected even predecessor scalar a_even, the even
2x2 determinant Delta_even, and the odd N=2 predecessor scalar needed for H3
ancestry.  Zero-containing determinant enclosures remain unresolved; they are
never promoted to root/contact existence.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post166_fb05_cell_interval import cell_coordinate_L_arb
from post173_fb05_q13_scalar_barrier import (
    PHYSICAL_QS,
    classify_scalar_interval,
    scalar_interval_json_record,
    scalar_interval_record_arb,
    scalar_record_arb_at_L,
    seam_overlap_record,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post173_fb05_q13_scalar_barrier_v1.json"


def _quantize_t(t_float: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(t_float) * den))
    num = max(1, min(den - 1, num))
    return num, den


def _point_record(Q: int, t_num: int, t_den: int, label: str) -> dict:
    t = arb(t_num) / t_den
    L = cell_coordinate_L_arb(Q, t)
    rec = scalar_record_arb_at_L(Q, L)
    classes = classify_scalar_interval({
        **rec,
        "t": t,
        "lo_num": t_num,
        "hi_num": t_num,
        "den": t_den,
    })
    even = rec["even"]
    return {
        "label": label,
        "Q": Q,
        "t_num": t_num,
        "t_den": t_den,
        "t": ball_record(t),
        "L": ball_record(L),
        "even": {
            "a": ball_record(even["a"]),
            "b": ball_record(even["b"]),
            "d": ball_record(even["d"]),
            "delta2": ball_record(even["delta2"]),
            "normalized_a": ball_record(even["normalized_a"]),
            "normalized_delta2": ball_record(even["normalized_delta2"]),
        },
        "odd_N2_predecessor": ball_record(rec["odd_N2_predecessor"]),
        "odd_N2_predecessor_normalized": ball_record(rec["odd_N2_predecessor_normalized"]),
        **classes,
        "claim_cap": "RIGOROUS_FINITE_POINT_SCALAR_AUDIT_ONLY",
    }


def _discovery_candidates(discovery: dict, bits: int) -> list[dict]:
    out = []
    seen = set()
    wanted = ("even_a", "even_delta2", "abs_even_delta2", "even_pivot", "odd_predecessor")
    for cell in discovery["cells"]:
        Q = int(cell["Q"])
        for metric in wanted:
            best = cell["metrics"][metric]["best"]
            num, den = _quantize_t(float(best["t"]), bits)
            key = (Q, num, den)
            if key in seen:
                continue
            seen.add(key)
            out.append(_point_record(Q, num, den, f"discovery_{metric}"))
    return out


def _terminal(classes: dict) -> bool:
    selected = classes["selected_classification"]
    ancestry = classes["odd_ancestry_classification"]
    if selected in ("EVEN_STRICT_POSITIVE_CERTIFIED", "EVEN_H1_LOSS_CERTIFIED"):
        return True
    if selected == "EVEN_BAD_INTERVAL_CERTIFIED" and ancestry != "ODD_N2_PREDECESSOR_UNRESOLVED":
        return True
    return False


def _adaptive_cell(Q: int, max_depth: int, max_leaf_budget: int) -> dict:
    stack: list[tuple[int, int, int, int]] = [(0, 1, 1, 0)]
    leaves: list[dict] = []
    evaluated = 0
    while stack and evaluated < max_leaf_budget:
        lo_num, hi_num, den, depth = stack.pop()
        try:
            rec = scalar_interval_record_arb(Q, lo_num, hi_num, den)
            j = scalar_interval_json_record(rec)
            j["depth"] = depth
            j["exception"] = None
        except Exception as exc:
            j = {
                "Q": Q,
                "t_interval": {"lo_num": lo_num, "hi_num": hi_num, "den": den},
                "depth": depth,
                "selected_classification": "EVEN_INTERVAL_EVALUATION_UNRESOLVED",
                "odd_ancestry_classification": "ODD_N2_PREDECESSOR_UNRESOLVED",
                "scope_classification": "SCALAR_INTERVAL_UNRESOLVED",
                "exception": repr(exc),
            }
        evaluated += 1
        if j["exception"] is None and _terminal(j):
            leaves.append(j)
            continue
        if depth >= max_depth:
            leaves.append(j)
            continue
        left_lo = 2 * lo_num
        mid = lo_num + hi_num
        right_hi = 2 * hi_num
        child_den = 2 * den
        stack.append((mid, right_hi, child_den, depth + 1))
        stack.append((left_lo, mid, child_den, depth + 1))

    pending_width = sum((hi - lo) / den for lo, hi, den, _depth in stack)
    widths: dict[str, float] = {}
    scopes: dict[str, float] = {}
    for leaf in leaves:
        t = leaf["t_interval"]
        width = (int(t["hi_num"]) - int(t["lo_num"])) / int(t["den"])
        cls = leaf["selected_classification"]
        scope = leaf["scope_classification"]
        widths[cls] = widths.get(cls, 0.0) + width
        scopes[scope] = scopes.get(scope, 0.0) + width
    unresolved_width = pending_width + sum(
        width for cls, width in widths.items()
        if cls not in ("EVEN_STRICT_POSITIVE_CERTIFIED", "EVEN_BAD_INTERVAL_CERTIFIED", "EVEN_H1_LOSS_CERTIFIED")
    )
    positive_width = widths.get("EVEN_STRICT_POSITIVE_CERTIFIED", 0.0)
    bad_width = widths.get("EVEN_BAD_INTERVAL_CERTIFIED", 0.0)
    h1_loss_width = widths.get("EVEN_H1_LOSS_CERTIFIED", 0.0)
    h3_bad_width = scopes.get("H3_FIRST_BAD_ALIGNED_INTERVAL_CERTIFIED", 0.0)

    bad_midpoints = []
    for leaf in leaves:
        if leaf["selected_classification"] != "EVEN_BAD_INTERVAL_CERTIFIED":
            continue
        t = leaf["t_interval"]
        num = int(t["lo_num"]) + int(t["hi_num"])
        den = 2 * int(t["den"])
        bad_midpoints.append(_point_record(Q, num, den, "bad_interval_midpoint_replay"))

    return {
        "Q": Q,
        "max_depth": max_depth,
        "max_leaf_budget": max_leaf_budget,
        "evaluated_intervals": evaluated,
        "leaf_count": len(leaves),
        "pending_interval_count": len(stack),
        "pending_width": pending_width,
        "selected_widths": widths,
        "scope_widths": scopes,
        "positive_width": positive_width,
        "bad_width": bad_width,
        "H1_loss_width": h1_loss_width,
        "H3_bad_width": h3_bad_width,
        "unresolved_width": unresolved_width,
        "whole_cell_selected_strict_positive_certified": positive_width == 1.0 and unresolved_width == 0.0,
        "selected_bad_interval_found": bad_width > 0.0,
        "H3_first_bad_aligned_interval_found": h3_bad_width > 0.0,
        "leaf_budget_exhausted": bool(stack),
        "leaves": leaves,
        "bad_interval_midpoint_replays": bad_midpoints,
    }


def _overall_classification(cells: list[dict]) -> str:
    if any(c["H3_first_bad_aligned_interval_found"] for c in cells):
        return "H3_FIRST_BAD_ALIGNED_REGION_CERTIFIED"
    if any(c["selected_bad_interval_found"] for c in cells):
        return "H2_SELECTED_BAD_REGION_CERTIFIED"
    if any(c["H1_loss_width"] > 0.0 for c in cells):
        return "H1_SCOPE_LOSS_REGION_CERTIFIED"
    if all(c["whole_cell_selected_strict_positive_certified"] for c in cells):
        return "STRICT_POSITIVE_Q13_CELL_CERTIFIED"
    determinant_unresolved = any(
        leaf.get("selected_classification") == "EVEN_DETERMINANT_SIGN_UNRESOLVED"
        for cell in cells for leaf in cell["leaves"]
    )
    if determinant_unresolved:
        return "CONTACT_OR_SIGN_UNRESOLVED"
    return "INTERVAL_DEPENDENCY_UNRESOLVED"


def _handoffs(cells: list[dict]) -> list[dict]:
    out = []
    for cell in cells:
        for point in cell["bad_interval_midpoint_replays"]:
            scope = point["scope_classification"]
            if scope not in ("H3_FIRST_BAD_ALIGNED_INTERVAL_CERTIFIED", "H2_SELECTED_BAD_SUCCESSOR_CERTIFIED"):
                continue
            out.append({
                "handoff": "POST166_SHIFTED_STATE",
                "scope": scope,
                "Q": point["Q"],
                "t_num": point["t_num"],
                "t_den": point["t_den"],
                "L": point["L"],
                "N": 2,
                "Kstar": 3,
                "selected_parity": "even",
            })
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--discovery", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST173_Q13_SCALAR_CERTIFICATE.json"))
    ap.add_argument("--precision-bits", type=int, default=None)
    ap.add_argument("--max-depth", type=int, default=None)
    ap.add_argument("--max-leaf-budget", type=int, default=None)
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    discovery = json.loads(args.discovery.read_text(encoding="utf-8"))
    precision = int(args.precision_bits or fixture.get("arb_precision_bits", 384))
    max_depth = int(args.max_depth or fixture["adaptive"]["max_depth"])
    max_leaf_budget = int(args.max_leaf_budget or fixture["adaptive"]["max_leaf_budget_per_cell"])
    point_bits = int(fixture.get("point_quantization_bits", 48))
    set_precision(precision)

    point_replays = _discovery_candidates(discovery, point_bits)
    seams = [seam_overlap_record(k) for k in (13, 14, 15, 16)]
    if not all(s["all_overlap"] for s in seams):
        raise AssertionError("scalar seam continuation mismatch")

    cells = [_adaptive_cell(Q, max_depth, max_leaf_budget) for Q in PHYSICAL_QS]
    overall = _overall_classification(cells)
    handoffs = _handoffs(cells)
    out = {
        "schema_version": "POST173_FB05_Q13_SCALAR_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_SCALAR_INTERVAL_AUDIT_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": precision,
        "max_depth": max_depth,
        "max_leaf_budget_per_cell": max_leaf_budget,
        "point_replays": point_replays,
        "seam_overlap_checks": seams,
        "physical_cells": cells,
        "overall_classification": overall,
        "shifted_state_handoffs": handoffs,
        "nonclaims": [
            "UNRESOLVED intervals are neither positive nor negative evidence.",
            "An interval enclosure containing Delta2=0 does not certify a root/contact point.",
            "H2 selected badness is not H3 first-bad ancestry unless the odd N=2 predecessor is also certified good.",
            "Strict positivity of this one q13 cell would be a finite method/structure result, not FB-05 closure.",
            "No output here is Lean theorem authority.",
            "RH remains OPEN."
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "overall_classification": overall,
        "precision_bits": precision,
        "cell_summaries": [
            {
                "Q": c["Q"],
                "positive_width": c["positive_width"],
                "bad_width": c["bad_width"],
                "H1_loss_width": c["H1_loss_width"],
                "H3_bad_width": c["H3_bad_width"],
                "unresolved_width": c["unresolved_width"],
                "leaf_budget_exhausted": c["leaf_budget_exhausted"],
            }
            for c in cells
        ],
        "handoffs": handoffs,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
