#!/usr/bin/env python3
"""Build the frozen dyadic benchmark schedule for the post-#175 fixed-unit test.

Discovery only.  This script does not certify interval-width improvement; it
materializes the determinant-minimum and pivot-minimum neighborhoods separately
and records the existing floating q13 scalar diagnostics at their centers.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post173_fb05_q13_scalar_barrier import scalar_record_float

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post175_fb05_q13_fixed_unit_enclosure_v1.json"


def _quantized_center(t: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(t) * den))
    num = max(1, min(den - 1, num))
    return num, den


def _box_from_center(label: str, Q: int, t: float, radius_bit: int, point_bits: int, primary: bool) -> dict:
    if radius_bit >= point_bits:
        raise ValueError("radius_bit must be smaller than point quantization bits")
    center_num, den = _quantized_center(t, point_bits)
    radius_num = 1 << (point_bits - radius_bit)
    lo = max(0, center_num - radius_num)
    hi = min(den, center_num + radius_num)
    if not 0 <= lo < hi <= den:
        raise AssertionError("invalid benchmark box")
    center_t = center_num / den
    import math
    L = math.log(float(Q)) + center_t * (math.log(float(Q + 1)) - math.log(float(Q)))
    even = scalar_record_float(L, "even")
    odd = scalar_record_float(L, "odd")
    return {
        "label": label,
        "Q": int(Q),
        "primary": bool(primary),
        "radius_bit": int(radius_bit),
        "lo_num": int(lo),
        "hi_num": int(hi),
        "den": int(den),
        "center_num": int(center_num),
        "center_t": center_t,
        "center_L_float": L,
        "center_even": even,
        "center_odd_N2_predecessor_normalized": odd["normalized_a"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST175_Q13_FIXED_UNIT_BENCHMARK.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    bits = int(fixture["point_quantization_bits"])
    boxes = []
    for center in fixture["primary_Q14_centers"]:
        for radius_bit in fixture["primary_radius_bits"]:
            boxes.append(_box_from_center(
                f"{center['label']}_r2^-{radius_bit}",
                int(center["Q"]), float(center["t"]), int(radius_bit), bits, True,
            ))
    for control in fixture["control_boxes"]:
        boxes.append(_box_from_center(
            control["label"], int(control["Q"]), float(control["t"]),
            int(control["radius_bit"]), bits, False,
        ))

    out = {
        "schema_version": "POST175_FB05_Q13_FIXED_UNIT_BENCHMARK_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_BENCHMARK_SCHEDULE_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "boxes": boxes,
        "primary_box_count": sum(1 for b in boxes if b["primary"]),
        "control_box_count": sum(1 for b in boxes if not b["primary"]),
        "nonclaims": fixture["nonclaims"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "primary_box_count": out["primary_box_count"],
        "control_box_count": out["control_box_count"],
        "primary_labels": [b["label"] for b in boxes if b["primary"]],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
