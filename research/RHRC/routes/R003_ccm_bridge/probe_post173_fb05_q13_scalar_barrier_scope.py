#!/usr/bin/env python3
"""High-resolution floating scout for the post-#173 q13 scalar barrier.

Discovery only: independently searches the even predecessor scalar a, the even
2x2 determinant Delta2, |Delta2|, the Schur pivot, and the odd N=2 predecessor
ancestry scalar on each physical Q=13/14/15 cell.  The odd K*=3 successor is
reported only as a supporting same-q/N parity control.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

from post173_fb05_q13_scalar_barrier import PHYSICAL_QS, scalar_record_float

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post173_fb05_q13_scalar_barrier_v1.json"


def _L_of_t(Q: int, t: float) -> float:
    lo = math.log(float(Q))
    hi = math.log(float(Q + 1))
    return lo + float(t) * (hi - lo)


def _point(Q: int, t: float) -> dict:
    L = _L_of_t(Q, t)
    even = scalar_record_float(L, "even")
    odd = scalar_record_float(L, "odd")
    return {
        "Q": Q,
        "t": float(t),
        "L": L,
        "even": even,
        "odd_N2_predecessor_scalar": odd["a"],
        "odd_N2_predecessor_normalized": odd["normalized_a"],
        "odd_successor_delta2": odd["delta2"],
        "odd_successor_normalized_delta2": odd["normalized_delta2"],
        "odd_successor_unit_shell_pivot": odd["unit_shell_pivot"],
    }


def _metric(rec: dict, name: str) -> float:
    e = rec["even"]
    if name == "even_a":
        return float(e["normalized_a"])
    if name == "even_delta2":
        return float(e["normalized_delta2"])
    if name == "abs_even_delta2":
        return abs(float(e["normalized_delta2"]))
    if name == "even_pivot":
        return float(e["unit_shell_pivot"])
    if name == "odd_predecessor":
        return float(rec["odd_N2_predecessor_normalized"])
    if name == "odd_successor_delta2":
        return float(rec["odd_successor_normalized_delta2"])
    raise ValueError(name)


def _optimize_metric(Q: int, name: str, grid: int, local_seeds: int) -> dict:
    ts = np.linspace(0.0, 1.0, grid)
    rows = [_point(Q, float(t)) for t in ts]
    order = sorted(range(len(rows)), key=lambda i: _metric(rows[i], name))
    candidates = [rows[order[0]]]
    used = set()
    for idx in order:
        if len(candidates) >= local_seeds + 1:
            break
        if idx <= 0 or idx >= len(rows) - 1:
            continue
        pair = (idx - 1, idx + 1)
        if pair in used:
            continue
        used.add(pair)
        lo = float(ts[idx - 1])
        hi = float(ts[idx + 1])
        res = minimize_scalar(
            lambda t: _metric(_point(Q, float(t)), name),
            bounds=(lo, hi),
            method="bounded",
            options={"xatol": 2e-14, "maxiter": 240},
        )
        if res.success and math.isfinite(float(res.fun)):
            candidates.append(_point(Q, float(res.x)))
    best = min(candidates, key=lambda r: _metric(r, name))
    return {"metric": name, "value": _metric(best, name), "best": best}


def _cell(Q: int, grid: int, local_seeds: int) -> dict:
    metrics = [
        "even_a",
        "even_delta2",
        "abs_even_delta2",
        "even_pivot",
        "odd_predecessor",
        "odd_successor_delta2",
    ]
    results = {name: _optimize_metric(Q, name, grid, local_seeds) for name in metrics}
    danger = results["even_delta2"]["best"]
    e = danger["even"]
    if e["normalized_a"] <= 0.0:
        sampled_scope = "SAMPLED_EVEN_H1_LOSS"
    elif e["normalized_delta2"] < 0.0:
        sampled_scope = (
            "SAMPLED_H3_FIRST_BAD_ALIGNED"
            if danger["odd_N2_predecessor_normalized"] > 0.0
            else "SAMPLED_H2_BAD_ONLY"
        )
    else:
        sampled_scope = "NO_SAMPLED_BAD_EVEN_SUCCESSOR"
    return {
        "Q": Q,
        "metrics": results,
        "sampled_scope_at_min_even_delta2": sampled_scope,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--grid", type=int, default=None)
    ap.add_argument("--local-seeds", type=int, default=None)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST173_Q13_SCALAR_DISCOVERY.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    grid = int(args.grid or fixture.get("float_grid", 257))
    local_seeds = int(args.local_seeds or fixture.get("float_local_seeds", 8))
    if grid < 33 or local_seeds < 1:
        raise ValueError("require grid>=33 and local_seeds>=1")

    cells = [_cell(Q, grid, local_seeds) for Q in PHYSICAL_QS]
    global_min_delta = min(
        (cell["metrics"]["even_delta2"]["best"] for cell in cells),
        key=lambda r: r["even"]["normalized_delta2"],
    )
    global_min_abs_delta = min(
        (cell["metrics"]["abs_even_delta2"]["best"] for cell in cells),
        key=lambda r: abs(r["even"]["normalized_delta2"]),
    )
    global_min_pivot = min(
        (cell["metrics"]["even_pivot"]["best"] for cell in cells),
        key=lambda r: r["even"]["unit_shell_pivot"],
    )
    global_min_odd_pred = min(
        (cell["metrics"]["odd_predecessor"]["best"] for cell in cells),
        key=lambda r: r["odd_N2_predecessor_normalized"],
    )

    out = {
        "schema_version": "POST173_FB05_Q13_SCALAR_DISCOVERY_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_Q13_SCALAR_DISCOVERY_ONLY",
        "target": fixture["selected_target"],
        "grid": grid,
        "local_seeds": local_seeds,
        "cells": cells,
        "global_candidates": {
            "min_even_delta2": global_min_delta,
            "min_abs_even_delta2": global_min_abs_delta,
            "min_even_pivot": global_min_pivot,
            "min_odd_N2_predecessor": global_min_odd_pred,
        },
        "nonclaims": [
            "Floating minima are discovery candidates, not exact minima.",
            "A floating sign change is not a rigorous sign certificate.",
            "The odd K*=3 successor is a supporting parity control, not an H3 substitute.",
            "H3 requires same-aperture smaller-size goodness in both parities.",
            "RH remains OPEN."
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "global_min_even_delta2": global_min_delta,
        "global_min_abs_even_delta2": global_min_abs_delta,
        "global_min_even_pivot": global_min_pivot,
        "global_min_odd_N2_predecessor": global_min_odd_pred,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
