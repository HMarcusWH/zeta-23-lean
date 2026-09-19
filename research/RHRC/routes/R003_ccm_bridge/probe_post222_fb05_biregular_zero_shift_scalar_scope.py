#!/usr/bin/env python3
"""Deterministic schedule replay for the post-#222 scalar audit.

No optimization or target-sign search occurs here.  The five centers are copied
verbatim from the checked-in post-#177 derivative fixture and then quantized to
one fixed dyadic grid for Arb replay.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post222_fb05_biregular_zero_shift_scalar_v1.json"


def _quantize(t: float, bits: int) -> tuple[int, int]:
    den = 1 << bits
    num = int(round(float(t) * den))
    num = max(1, min(den - 1, num))
    return num, den


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST222_BIREGULAR_SCALAR_SCHEDULE.json"))
    args = ap.parse_args()

    fx = json.loads(args.input.read_text(encoding="utf-8"))
    source = HERE / "fixtures" / fx["source_schedule_fixture"]
    src = json.loads(source.read_text(encoding="utf-8"))

    inherited = fx["inherited_points"]
    assert src["derivative_check_points"] == inherited, (
        "post-#222 schedule drifted from the frozen post-#177 derivative centers"
    )
    labels = [p["label"] for p in inherited]
    assert labels == fx["selected_center_labels"]

    bits = int(fx["point_quantization_bits"])
    rows = []
    for p in inherited:
        num, den = _quantize(float(p["t"]), bits)
        rows.append({
            "label": p["label"],
            "Q": int(p["Q"]),
            "t_source": float(p["t"]),
            "t_num": num,
            "t_den": den,
            "selection_basis": "INHERITED_POST177_CENTER_ONLY",
        })

    out = {
        "schema_version": "POST222_FB05_BIREGULAR_ZERO_SHIFT_SCALAR_SCHEDULE_v1",
        "status": "PASS",
        "source_schedule_fixture": fx["source_schedule_fixture"],
        "point_quantization_bits": bits,
        "points": rows,
        "adaptive_point_search": False,
        "target_sign_selection": False,
        "claim_cap": "FROZEN_SCHEDULE_ONLY",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
