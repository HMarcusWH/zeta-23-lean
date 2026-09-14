#!/usr/bin/env python3
"""Rigorous finite derivative discrimination for the post-#177 Q14 laboratory.

The certificate classifies derivative *information*, not RH.  A green run may
return BRACKETED, PARTIAL, or UNRESOLVED.  Only malformed scope, execution, or
normalization regressions are CI failures.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, definitely_negative, definitely_positive, set_precision
from post177_fb05_q13_fixed_unit_derivative import (
    fixed_unit_derivative_scalar_interval_record_arb,
)
from probe_post177_fb05_q13_fixed_unit_derivative_scope import expected_boxes

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post177_fb05_q13_fixed_unit_derivative_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    if schedule.get("schema_version") != "POST177_FB05_Q13_FIXED_UNIT_DERIVATIVE_SCHEDULE_v1":
        raise AssertionError("derivative schedule schema regression")
    if schedule.get("status") != "PASS":
        raise AssertionError("derivative schedule did not pass")
    for key in ("theorem_authority_pr", "research_anchor_pr", "routing_sync_pr"):
        if schedule.get(key) != fixture.get(key):
            raise AssertionError(f"derivative schedule authority mismatch: {key}")

    expected = expected_boxes(fixture)
    actual = schedule.get("boxes")
    if not isinstance(actual, list) or len(actual) != len(expected):
        raise AssertionError("derivative schedule box count mismatch")
    expected_by_label = {b["label"]: b for b in expected}
    labels = [b.get("label") for b in actual]
    if len(set(labels)) != len(labels) or set(labels) != set(expected_by_label):
        raise AssertionError("derivative schedule label mismatch")
    keys = (
        "label", "Q", "role", "primary", "side", "offset_bit", "radius_bit",
        "center_num", "lo_num", "hi_num", "den",
    )
    for box in actual:
        exp = expected_by_label[box["label"]]
        for key in keys:
            if box.get(key) != exp.get(key):
                raise AssertionError(f"derivative schedule mismatch for {box['label']} field {key}")
    primary_count = sum(1 for b in expected if b["primary"])
    if schedule.get("primary_box_count") != primary_count:
        raise AssertionError("derivative primary count mismatch")
    if schedule.get("control_box_count") != len(expected) - primary_count:
        raise AssertionError("derivative control count mismatch")


def _sign(x: arb) -> str:
    if definitely_positive(x):
        return "POSITIVE_CERTIFIED"
    if definitely_negative(x):
        return "NEGATIVE_CERTIFIED"
    return "UNRESOLVED"


def _value_scope(rec: dict) -> dict:
    a = rec["even"]["a"]
    delta = rec["even"]["delta2"]
    odd = rec["odd_N2_predecessor"]
    a_sign = _sign(a)
    delta_sign = _sign(delta)
    odd_sign = _sign(odd)
    if a_sign == "NEGATIVE_CERTIFIED":
        selected = "EVEN_H1_LOSS_CERTIFIED"
    elif a_sign != "POSITIVE_CERTIFIED":
        selected = "EVEN_H1_UNRESOLVED"
    elif delta_sign == "NEGATIVE_CERTIFIED":
        selected = "EVEN_BAD_INTERVAL_CERTIFIED"
    elif delta_sign == "POSITIVE_CERTIFIED":
        selected = "EVEN_STRICT_POSITIVE_CERTIFIED"
    else:
        selected = "EVEN_DETERMINANT_SIGN_UNRESOLVED"
    if odd_sign == "POSITIVE_CERTIFIED":
        ancestry = "ODD_N2_PREDECESSOR_POSITIVE_CERTIFIED"
    elif odd_sign == "NEGATIVE_CERTIFIED":
        ancestry = "ODD_N2_PREDECESSOR_NEGATIVE_CERTIFIED"
    else:
        ancestry = "ODD_N2_PREDECESSOR_UNRESOLVED"
    return {
        "selected": selected,
        "odd_ancestry": ancestry,
        "a_sign": a_sign,
        "delta2_sign": delta_sign,
        "odd_predecessor_sign": odd_sign,
    }


def _box_record(box: dict) -> dict:
    rec = fixed_unit_derivative_scalar_interval_record_arb(
        int(box["Q"]), int(box["lo_num"]), int(box["hi_num"]), int(box["den"])
    )
    even = rec["even"]
    derivative_sign = _sign(even["delta2_prime"])

    pivot_prime = None
    pivot_prime_sign = "OUT_OF_H1_SCOPE"
    if definitely_positive(even["a"]):
        pivot_prime = (
            even["delta2_prime"] * even["a"]
            - even["delta2"] * even["a_prime"]
        ) / (even["a"] ** 2)
        pivot_prime_sign = _sign(pivot_prime)

    return {
        "label": box["label"],
        "Q": int(box["Q"]),
        "role": box["role"],
        "primary": bool(box["primary"]),
        "side": box.get("side"),
        "offset_bit": box.get("offset_bit"),
        "radius_bit": int(box["radius_bit"]),
        "t_interval": {
            "lo_num": int(box["lo_num"]),
            "hi_num": int(box["hi_num"]),
            "den": int(box["den"]),
            "ball": ball_record(rec["t"]),
        },
        "L_ball": ball_record(rec["L"]),
        "value_scope": _value_scope(rec),
        "even": {
            "a": ball_record(even["a"]),
            "b": ball_record(even["b"]),
            "d": ball_record(even["d"]),
            "delta2": ball_record(even["delta2"]),
            "a_prime": ball_record(even["a_prime"]),
            "b_prime": ball_record(even["b_prime"]),
            "d_prime": ball_record(even["d_prime"]),
            "delta2_prime": ball_record(even["delta2_prime"]),
            "delta2_prime_sign": derivative_sign,
            "pivot_prime": None if pivot_prime is None else ball_record(pivot_prime),
            "pivot_prime_sign": pivot_prime_sign,
        },
        "odd_N2_predecessor": ball_record(rec["odd_N2_predecessor"]),
        "odd_N2_predecessor_prime": ball_record(rec["odd_N2_predecessor_prime"]),
    }


def _classify_derivative(records: list[dict]) -> dict:
    primary = [r for r in records if r["primary"] and r["role"] == "side"]
    left_neg = [r for r in primary if r["side"] == "left" and r["even"]["delta2_prime_sign"] == "NEGATIVE_CERTIFIED"]
    left_pos = [r for r in primary if r["side"] == "left" and r["even"]["delta2_prime_sign"] == "POSITIVE_CERTIFIED"]
    right_neg = [r for r in primary if r["side"] == "right" and r["even"]["delta2_prime_sign"] == "NEGATIVE_CERTIFIED"]
    right_pos = [r for r in primary if r["side"] == "right" and r["even"]["delta2_prime_sign"] == "POSITIVE_CERTIFIED"]

    minimum_oriented = bool(left_neg and right_pos)
    maximum_oriented = bool(left_pos and right_neg)
    if minimum_oriented and not maximum_oriented:
        disposition = "DERIVATIVE_BASIN_BRACKETED"
        orientation = "MINIMUM_ORIENTED"
    elif maximum_oriented and not minimum_oriented:
        disposition = "DERIVATIVE_BASIN_BRACKETED"
        orientation = "MAXIMUM_ORIENTED"
    elif minimum_oriented and maximum_oriented:
        disposition = "DERIVATIVE_PARTIAL"
        orientation = "MULTIPLE_ORIENTATIONS_SAMPLED"
    elif any(r["even"]["delta2_prime_sign"] != "UNRESOLVED" for r in primary):
        disposition = "DERIVATIVE_PARTIAL"
        orientation = "NO_TWO_SIDED_BRACKET"
    else:
        disposition = "DERIVATIVE_UNRESOLVED"
        orientation = "NO_CERTIFIED_PRIMARY_DERIVATIVE_SIGN"

    return {
        "disposition": disposition,
        "orientation": orientation,
        "left_negative_labels": [r["label"] for r in left_neg],
        "left_positive_labels": [r["label"] for r in left_pos],
        "right_negative_labels": [r["label"] for r in right_neg],
        "right_positive_labels": [r["label"] for r in right_pos],
        "derived_stationary_existence_if_continuity_used": bool(
            disposition == "DERIVATIVE_BASIN_BRACKETED"
        ),
        "uniqueness_claim": False,
    }


def _classify_value_event(records: list[dict]) -> dict:
    bad = [r["label"] for r in records if r["value_scope"]["selected"] == "EVEN_BAD_INTERVAL_CERTIFIED"]
    h1_loss = [r["label"] for r in records if r["value_scope"]["selected"] == "EVEN_H1_LOSS_CERTIFIED"]
    if bad:
        event = "BAD_INTERVAL_CERTIFIED"
    elif h1_loss:
        event = "H1_SCOPE_LOSS_CERTIFIED"
    else:
        event = "NO_BAD_OR_H1_LOSS_INTERVAL_CERTIFIED"
    return {"event": event, "bad_labels": bad, "h1_loss_labels": h1_loss}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST177_Q14_DERIVATIVE_CERTIFICATE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)
    set_precision(int(fixture["arb_precision_bits"]))

    records = [_box_record(box) for box in schedule["boxes"]]
    derivative = _classify_derivative(records)
    value_event = _classify_value_event(records)

    out = {
        "schema_version": "POST177_FB05_Q13_FIXED_UNIT_DERIVATIVE_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_DERIVATIVE_DISCRIMINATION_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": int(fixture["arb_precision_bits"]),
        "schedule_bound_to_fixture": True,
        "derivative_classification": derivative,
        "value_event": value_event,
        "boxes": records,
        "nonclaims": fixture["nonclaims"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "derivative_classification": derivative,
        "value_event": value_event,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
