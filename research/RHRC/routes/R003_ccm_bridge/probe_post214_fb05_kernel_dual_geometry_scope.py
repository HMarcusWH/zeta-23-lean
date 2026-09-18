#!/usr/bin/env python3
"""Freeze the post-#214 kernel-dual-geometry schedule from inherited centers.

The three points are not discovered here.  They are the exact dyadic
quantizations of Q13_midpoint, Q14_determinant_basin, and Q15_midpoint already
present in the post-#177 fixture and explicitly named again by the post-#202
implementation-check fixture.

The optional fast records are discovery diagnostics only.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post214_fb05_kernel_dual_geometry import geometry_record_float

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post214_fb05_kernel_dual_geometry_v1.json"


def _quantized_center(t: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(t) * den))
    num = max(1, min(den - 1, num))
    return num, den


def kernel_dual_geometry_schedule(fixture: dict) -> dict:
    post177 = json.loads(
        (HERE / "fixtures" / fixture["inherited_post177_fixture"]).read_text(encoding="utf-8")
    )
    post202 = json.loads(
        (HERE / "fixtures" / fixture["inherited_post202_fixture"]).read_text(encoding="utf-8")
    )
    labels = list(fixture["selected_center_labels"])
    if labels != list(post202["implementation_check_labels"]):
        raise AssertionError("post-#214 center labels drifted from post-#202 implementation checks")

    point_map = {row["label"]: row for row in post177["derivative_check_points"]}
    if any(label not in point_map for label in labels):
        raise AssertionError("selected inherited center is missing from post-#177 fixture")

    bits = int(post177["point_quantization_bits"])
    primary_label = fixture["primary_center_label"]
    centers = []
    for label in labels:
        src = point_map[label]
        num, den = _quantized_center(float(src["t"]), bits)
        center_t = num / den
        row = {
            "label": label,
            "Q": int(src["Q"]),
            "center_num": int(num),
            "den": int(den),
            "center_t": center_t,
            "primary": label == primary_label,
            "role": "primary" if label == primary_label else "adjacent_Q_control",
        }
        row["fast_probe"] = geometry_record_float(row["Q"], center_t)
        centers.append(row)

    if sum(bool(row["primary"]) for row in centers) != 1:
        raise AssertionError("expected exactly one preregistered primary center")
    return {
        "schema_version": "POST214_FB05_KERNEL_DUAL_GEOMETRY_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "base_main_sha": fixture["base_main_sha"],
        "base_main_tree": fixture["base_main_tree"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "latest_research_authority_pr": fixture["latest_research_authority_pr"],
        "selected_target": fixture["selected_target"],
        "point_quantization_bits": bits,
        "arb_precision_bits": int(fixture["arb_precision_bits"]),
        "implementation_check_precision_bits": int(fixture["implementation_check_precision_bits"]),
        "centers": centers,
        "policy": fixture["policy"],
        "nonclaims": fixture["nonclaims"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST214_FB05_KERNEL_DUAL_GEOMETRY_SCHEDULE.json"),
    )
    args = ap.parse_args()
    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    out = kernel_dual_geometry_schedule(fixture)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "centers": [
            {
                "label": row["label"],
                "Q": row["Q"],
                "center_num": row["center_num"],
                "den": row["den"],
                "primary": row["primary"],
                "fast_wedge": row["fast_probe"]["wedge"],
                "fast_R_min": row["fast_probe"]["generalized_R_min"],
                "fast_R_max": row["fast_probe"]["generalized_R_max"],
            }
            for row in out["centers"]
        ],
        "adaptive_point_search": False,
        "claim_cap": out["claim_cap"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
