#!/usr/bin/env python3
"""Build the frozen Q14 derivative-discrimination schedule after PR #177.

Discovery only.  The schedule is fixture-determined and uses exact dyadic
coordinates.  No derivative sign or stationary-point claim is certified here.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def _quantized_center(t: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(t) * den))
    num = max(1, min(den - 1, num))
    return num, den


def _box_from_center(
    label: str,
    Q: int,
    t: float,
    radius_bit: int,
    point_bits: int,
    role: str,
    primary: bool,
    side: str | None = None,
    offset_bit: int | None = None,
) -> dict:
    if radius_bit >= point_bits:
        raise ValueError("radius_bit must be smaller than point quantization bits")
    center_num, den = _quantized_center(t, point_bits)
    radius_num = 1 << (point_bits - radius_bit)
    lo = max(0, center_num - radius_num)
    hi = min(den, center_num + radius_num)
    if not 0 <= lo < hi <= den:
        raise AssertionError("invalid derivative benchmark box")
    return {
        "label": label,
        "Q": int(Q),
        "role": role,
        "primary": bool(primary),
        "side": side,
        "offset_bit": offset_bit,
        "radius_bit": int(radius_bit),
        "center_num": int(center_num),
        "lo_num": int(lo),
        "hi_num": int(hi),
        "den": int(den),
        "center_t": center_num / den,
    }


def expected_boxes(fixture: dict) -> list[dict]:
    bits = int(fixture["point_quantization_bits"])
    center = fixture["determinant_center"]
    Q = int(center["Q"])
    t0 = float(center["t"])
    extra = int(fixture["primary_radius_extra_bits"])
    boxes: list[dict] = []

    for offset_bit in fixture["primary_offset_bits"]:
        offset_bit = int(offset_bit)
        offset = 2.0 ** (-offset_bit)
        radius_bit = offset_bit + extra
        boxes.append(_box_from_center(
            f"det_left_o2^-{offset_bit}_r2^-{radius_bit}", Q, t0 - offset,
            radius_bit, bits, "side", True, "left", offset_bit,
        ))
        boxes.append(_box_from_center(
            f"det_right_o2^-{offset_bit}_r2^-{radius_bit}", Q, t0 + offset,
            radius_bit, bits, "side", True, "right", offset_bit,
        ))

    for radius_bit in fixture["central_radius_bits"]:
        radius_bit = int(radius_bit)
        boxes.append(_box_from_center(
            f"det_center_r2^-{radius_bit}", Q, t0,
            radius_bit, bits, "central", False,
        ))

    pivot = fixture["pivot_center_control"]
    boxes.append(_box_from_center(
        pivot["label"], int(pivot["Q"]), float(pivot["t"]),
        int(pivot["radius_bit"]), bits, "pivot_control", False,
    ))

    for control in fixture["control_boxes"]:
        boxes.append(_box_from_center(
            control["label"], int(control["Q"]), float(control["t"]),
            int(control["radius_bit"]), bits, "control", False,
        ))
    return boxes


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST177_Q14_DERIVATIVE_SCHEDULE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    boxes = expected_boxes(fixture)
    out = {
        "schema_version": "POST177_FB05_Q13_FIXED_UNIT_DERIVATIVE_SCHEDULE_v1",
        "status": "PASS",
        "claim_cap": "EXPERIMENTAL_DERIVATIVE_SCHEDULE_ONLY",
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
