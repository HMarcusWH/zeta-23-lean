#!/usr/bin/env python3
"""Floating falsifier for threshold-to-threshold Schur barrier dynamics.

The scout prioritizes direct physical minima and the exact cell budget

    Delta P_full = Delta P_background + A_q,

where A_q is the exact nonlinear Schur lift of the current q atom.  Envelope
integration is recorded only as a secondary channel-attribution diagnostic.
All output is experimental research evidence only.  RH remains OPEN.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post171_fb05_schur_barrier import barrier_case

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post171_fb05_threshold_barrier_v1.json"


def _compact_case(rec: dict) -> dict:
    out = dict(rec)
    for key in ("physical_minimum", "background_minimum"):
        sub = dict(out[key])
        sub.pop("grid_rows", None)
        out[key] = sub
    integ = dict(out["background_channel_integration"])
    if integ.get("records") is not None:
        integ["records"] = [
            {
                "omega": r.get("omega"),
                "h": r.get("h"),
                "available": r.get("available"),
                "channel_directional_contributions": r.get("channel_directional_contributions"),
                "directional_total": r.get("directional_total"),
            }
            for r in integ["records"]
        ]
    out["background_channel_integration"] = integ
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--grid", type=int, default=97)
    ap.add_argument("--local-seeds", type=int, default=6)
    ap.add_argument("--integration-nodes", type=int, default=10)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST171_FB05_THRESHOLD_BARRIER_DISCOVERY.json"))
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))

    cases = []
    for target in fixture["stress_targets"]:
        rec = barrier_case(
            int(target["q"]),
            int(target["predecessor_N"]),
            target["selected_parity"],
            grid=args.grid,
            local_seeds=args.local_seeds,
            integration_nodes=args.integration_nodes,
        )
        cases.append(_compact_case(rec))

    counts: dict[str, int] = {}
    for rec in cases:
        counts[rec["classification"]] = counts.get(rec["classification"], 0) + 1

    dangerous = sorted(
        [c for c in cases if c["physical_minimum"].get("best") is not None],
        key=lambda c: float(c["physical_minimum"]["best"]["unit_full_pivot"]),
    )
    bad = [c for c in cases if c["classification"] == "SAMPLED_BAD_SUCCESSOR"]

    payload = {
        "schema_version": "POST171_FB05_THRESHOLD_BARRIER_DISCOVERY_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_THRESHOLD_TO_THRESHOLD_BARRIER_SIGNAL_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "configuration": {
            "grid": args.grid,
            "local_seeds": args.local_seeds,
            "integration_nodes": args.integration_nodes,
        },
        "classification_counts": counts,
        "cases": cases,
        "most_dangerous_cases": dangerous,
        "sampled_bad_successor_cases": bad,
        "nonclaims": [
            "A sampled positive minimum is not whole-cell positivity.",
            "Envelope integration is a floating cancellation diagnostic, not theorem authority.",
            "H1 interpretation is restricted to predecessor-positive states.",
            "The current-q accumulated lift is not an instantaneous jump at the next seam.",
            "No global Schur monotonicity is assumed.",
            "RH remains OPEN."
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    print(json.dumps({
        "status": "PASS",
        "classification_counts": counts,
        "most_dangerous": [
            {
                "target": c["target"],
                "classification": c["classification"],
                "minimum_unit_full_pivot": c["physical_minimum"]["best"]["unit_full_pivot"] if c["physical_minimum"].get("best") else None,
                "minimum_omega": c["physical_minimum"]["best"]["omega"] if c["physical_minimum"].get("best") else None,
                "headroom_ratio": c["headroom_ratio"],
                "entry_lift_at_minimum": c["unit_entry_lift_at_physical_minimum"],
                "background_drawdown": c["unit_background_drawdown_to_background_minimum"],
                "integration_closure_residual": c["background_channel_integration"].get("channel_sum_minus_direct_change") if c["background_channel_integration"].get("available") else None,
                "cancellation_ratio": c["background_channel_integration"].get("cancellation_ratio") if c["background_channel_integration"].get("available") else None,
            }
            for c in dangerous
        ],
        "sampled_bad_successor_count": len(bad),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
