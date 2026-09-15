#!/usr/bin/env python3
"""Rigorous finite correlation-preserving derivative discrimination after PR #179.

A green run certifies that the frozen experiment executed faithfully. Research
outcomes such as unresolved point signs or no Schur width gain remain legitimate
green falsification results. Only malformed scope, schedule drift, algebraic
disagreement, or execution/normalization regressions are red conditions.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post179_fb05_q13_correlation_preserving_derivative import (
    arb_width,
    interval_record_from_box,
    overlap,
    point_record_from_box,
    sign_class,
)
from probe_post179_fb05_q13_correlation_preserving_derivative_scope import inherited_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post179_fb05_q13_correlation_preserving_derivative_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = inherited_schedule(fixture)
    for key in (
        "schema_version",
        "status",
        "theorem_authority_pr",
        "research_anchor_pr",
        "routing_sync_pr",
        "source_fixture_schema_version",
        "primary_box_count",
        "control_box_count",
    ):
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#179 schedule mismatch: {key}")

    actual = schedule.get("boxes")
    wanted = expected["boxes"]
    if not isinstance(actual, list) or len(actual) != len(wanted):
        raise AssertionError("post-#179 schedule box count mismatch")
    expected_by_label = {b["label"]: b for b in wanted}
    labels = [b.get("label") for b in actual]
    if len(set(labels)) != len(labels) or set(labels) != set(expected_by_label):
        raise AssertionError("post-#179 schedule label mismatch")
    keys = (
        "label", "Q", "role", "primary", "side", "offset_bit", "radius_bit",
        "center_num", "lo_num", "hi_num", "den",
    )
    for box in actual:
        exp = expected_by_label[box["label"]]
        for key in keys:
            if box.get(key) != exp.get(key):
                raise AssertionError(f"post-#179 schedule drift for {box['label']} field {key}")


def _value_scope(interval: dict) -> dict:
    rec = interval["record"]
    even = rec["even"]
    a_sign = sign_class(even["a"])
    delta_sign = sign_class(even["delta2"])
    odd_sign = sign_class(rec["odd_N2_predecessor"])
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


def _serialize_schur(schur: dict) -> dict:
    if not schur["h1_certified"]:
        return {
            "h1_certified": False,
            "scope": schur["scope"],
        }
    return {
        "h1_certified": True,
        "scope": schur["scope"],
        "x": ball_record(schur["x"]),
        "pivot": ball_record(schur["pivot"]),
        "pivot_prime_directional": ball_record(schur["pivot_prime_directional"]),
        "pivot_prime_quotient": ball_record(schur["pivot_prime_quotient"]),
        "delta2_factorized": ball_record(schur["delta2_factorized"]),
        "delta2_prime_factorized": ball_record(schur["delta2_prime_factorized"]),
        "delta2_prime_sign": sign_class(schur["delta2_prime_factorized"]),
        "delta2_overlap": bool(schur["delta2_overlap"]),
        "delta2_prime_overlap": bool(schur["delta2_prime_overlap"]),
        "pivot_prime_overlap": bool(schur["pivot_prime_overlap"]),
    }


def _box_record(box: dict, fixture: dict) -> dict:
    point = point_record_from_box(box)
    interval = interval_record_from_box(box)

    if not overlap(point["raw_delta2_prime"], interval["raw_delta2_prime"]):
        raise AssertionError(f"point/raw-box derivative mismatch: {box['label']}")

    point_schur = point["schur"]
    box_schur = interval["schur"]
    for context, schur in (("point", point_schur), ("box", box_schur)):
        if schur["h1_certified"]:
            if not schur["delta2_overlap"]:
                raise AssertionError(f"{context} determinant factorization mismatch: {box['label']}")
            if not schur["delta2_prime_overlap"]:
                raise AssertionError(f"{context} derivative factorization mismatch: {box['label']}")
            if not schur["pivot_prime_overlap"]:
                raise AssertionError(f"{context} pivot derivative mismatch: {box['label']}")

    point_schur_sign = "OUT_OF_H1_SCOPE"
    if point_schur["h1_certified"]:
        point_schur_sign = sign_class(point_schur["delta2_prime_factorized"])

    schur_box_sign = "OUT_OF_H1_SCOPE"
    width_cmp = None
    if box_schur["h1_certified"]:
        schur_box_sign = sign_class(box_schur["delta2_prime_factorized"])
        if point_schur["h1_certified"] and not overlap(
            point_schur["delta2_prime_factorized"],
            box_schur["delta2_prime_factorized"],
        ):
            raise AssertionError(f"point/Schur-box derivative mismatch: {box['label']}")

        raw_w = arb_width(interval["raw_delta2_prime"])
        schur_w = arb_width(box_schur["delta2_prime_factorized"])
        factor = arb(str(fixture["material_width_gain_factor"]))
        width_cmp = {
            "raw_width": ball_record(raw_w),
            "schur_width": ball_record(schur_w),
            "strictly_narrower": bool(schur_w < raw_w),
            "material_2x_gain": bool(factor * schur_w <= raw_w),
        }
        if bool(schur_w > 0):
            width_cmp["gain_raw_over_schur"] = ball_record(raw_w / schur_w)
        else:
            width_cmp["gain_raw_over_schur"] = {"infinite_or_exact": True}

    raw_box_sign = sign_class(interval["raw_delta2_prime"])
    sign_recovery = bool(
        raw_box_sign == "UNRESOLVED"
        and schur_box_sign in ("NEGATIVE_CERTIFIED", "POSITIVE_CERTIFIED")
    )

    return {
        "label": box["label"],
        "Q": int(box["Q"]),
        "role": box["role"],
        "primary": bool(box["primary"]),
        "side": box.get("side"),
        "offset_bit": box.get("offset_bit"),
        "radius_bit": int(box["radius_bit"]),
        "exact_center": {
            "center_num": int(box["center_num"]),
            "den": int(box["den"]),
            "t": ball_record(point["t"]),
            "L": ball_record(point["L"]),
            "raw_delta2_prime": ball_record(point["raw_delta2_prime"]),
            "raw_delta2_prime_sign": point["raw_delta2_prime_sign"],
            "schur_delta2_prime_sign": point_schur_sign,
            "schur": _serialize_schur(point_schur),
        },
        "interval": {
            "lo_num": int(box["lo_num"]),
            "hi_num": int(box["hi_num"]),
            "den": int(box["den"]),
            "t": ball_record(interval["t"]),
            "L": ball_record(interval["L"]),
            "raw_delta2_prime": ball_record(interval["raw_delta2_prime"]),
            "raw_delta2_prime_sign": raw_box_sign,
            "schur_delta2_prime_sign": schur_box_sign,
            "schur": _serialize_schur(box_schur),
            "width_comparison": width_cmp,
            "sign_recovery": sign_recovery,
        },
        "value_scope": _value_scope(interval),
        "odd_N2_predecessor": ball_record(interval["record"]["odd_N2_predecessor"]),
    }


def _orientation(records: list[dict], sign_path: tuple[str, ...], out_of_scope: str | None = None) -> dict:
    primary = [r for r in records if r["primary"] and r["role"] == "side"]

    def get_sign(rec: dict) -> str:
        x = rec
        for key in sign_path:
            x = x[key]
        return x

    usable = [r for r in primary if out_of_scope is None or get_sign(r) != out_of_scope]
    left_neg = [r["label"] for r in usable if r["side"] == "left" and get_sign(r) == "NEGATIVE_CERTIFIED"]
    left_pos = [r["label"] for r in usable if r["side"] == "left" and get_sign(r) == "POSITIVE_CERTIFIED"]
    right_neg = [r["label"] for r in usable if r["side"] == "right" and get_sign(r) == "NEGATIVE_CERTIFIED"]
    right_pos = [r["label"] for r in usable if r["side"] == "right" and get_sign(r) == "POSITIVE_CERTIFIED"]
    return {
        "left_negative_labels": left_neg,
        "left_positive_labels": left_pos,
        "right_negative_labels": right_neg,
        "right_positive_labels": right_pos,
        "minimum_oriented": bool(left_neg and right_pos),
        "maximum_oriented": bool(left_pos and right_neg),
        "usable_primary_count": len(usable),
    }


def _classify_point(records: list[dict]) -> dict:
    raw = _orientation(records, ("exact_center", "raw_delta2_prime_sign"))
    schur = _orientation(
        records,
        ("exact_center", "schur_delta2_prime_sign"),
        out_of_scope="OUT_OF_H1_SCOPE",
    )

    if raw["minimum_oriented"] and not raw["maximum_oriented"]:
        disposition = "POINT_DERIVATIVE_BASIN_BRACKETED"
        orientation = "MINIMUM_ORIENTED"
    elif raw["maximum_oriented"] and not raw["minimum_oriented"]:
        disposition = "POINT_DERIVATIVE_BASIN_BRACKETED"
        orientation = "MAXIMUM_ORIENTED"
    elif any(
        r["exact_center"]["raw_delta2_prime_sign"] != "UNRESOLVED"
        for r in records if r["primary"] and r["role"] == "side"
    ):
        disposition = "POINT_DERIVATIVE_PARTIAL"
        orientation = "NO_TWO_SIDED_RAW_POINT_BRACKET"
    else:
        disposition = "POINT_DERIVATIVE_UNRESOLVED"
        orientation = "NO_CERTIFIED_RAW_POINT_SIGN"

    return {
        "disposition": disposition,
        "orientation": orientation,
        "raw_orientation": raw,
        "schur_point_orientation": schur,
        "derived_stationary_existence_if_continuity_used": bool(
            disposition == "POINT_DERIVATIVE_BASIN_BRACKETED"
        ),
        "uniqueness_claim": False,
    }


def _classify_representation(records: list[dict]) -> dict:
    orientation = _orientation(
        records,
        ("interval", "schur_delta2_prime_sign"),
        out_of_scope="OUT_OF_H1_SCOPE",
    )
    primary = [r for r in records if r["primary"] and r["role"] == "side"]
    applicable = [r for r in primary if r["interval"]["width_comparison"] is not None]
    sign_recovery = [r["label"] for r in applicable if r["interval"]["sign_recovery"]]
    strict_gain = [
        r["label"] for r in applicable
        if r["interval"]["width_comparison"]["strictly_narrower"]
    ]
    material_gain = [
        r["label"] for r in applicable
        if r["interval"]["width_comparison"]["material_2x_gain"]
    ]

    if not applicable:
        disposition = "SCHUR_OUT_OF_H1_SCOPE"
    elif orientation["minimum_oriented"] and not orientation["maximum_oriented"]:
        disposition = "SCHUR_BASIN_BRACKETED"
    elif sign_recovery:
        disposition = "SCHUR_SIGN_RECOVERY"
    elif len(material_gain) == len(applicable):
        disposition = "SCHUR_WIDTH_GAIN"
    elif strict_gain:
        disposition = "SCHUR_MIXED"
    else:
        disposition = "NO_SCHUR_GAIN"

    return {
        "disposition": disposition,
        "orientation": orientation,
        "applicable_primary_count": len(applicable),
        "primary_count": len(primary),
        "sign_recovery_labels": sign_recovery,
        "strict_width_gain_labels": strict_gain,
        "material_2x_gain_labels": material_gain,
        "derived_stationary_existence_if_continuity_used": bool(
            disposition == "SCHUR_BASIN_BRACKETED"
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
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST179_Q14_CORRELATION_CERTIFICATE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)
    set_precision(int(fixture["arb_precision_bits"]))

    records = [_box_record(box, fixture) for box in schedule["boxes"]]
    point_disposition = _classify_point(records)
    representation_disposition = _classify_representation(records)
    value_event = _classify_value_event(records)

    out = {
        "schema_version": "POST179_FB05_Q13_CORRELATION_PRESERVING_DERIVATIVE_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": "RIGOROUS_FINITE_CORRELATION_PRESERVING_DERIVATIVE_DISCRIMINATION_ONLY",
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": int(fixture["arb_precision_bits"]),
        "schedule_bound_to_post177_fixture": True,
        "point_disposition": point_disposition,
        "representation_disposition": representation_disposition,
        "value_event": value_event,
        "boxes": records,
        "nonclaims": fixture["nonclaims"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "point_disposition": point_disposition,
        "representation_disposition": representation_disposition,
        "value_event": value_event,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
