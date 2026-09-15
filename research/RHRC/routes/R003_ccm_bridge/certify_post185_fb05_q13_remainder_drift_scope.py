#!/usr/bin/env python3
"""Rigorous finite remainder-drift falsification after routing sync PR #185.

A green run certifies faithful execution and internal enclosure consistency.
The mathematical disposition may be strong, mixed, failed, or unresolved; all
four are legitimate research outcomes. RH remains OPEN.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from canonical_source_arb import ball_record, set_precision
from post179_fb05_q13_correlation_preserving_derivative import sign_class
from post185_fb05_q13_remainder_drift import (
    interval_remainder_drift_record,
    point_remainder_drift_record,
)
from probe_post185_fb05_q13_remainder_drift_scope import frozen_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post185_fb05_q13_remainder_drift_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = frozen_schedule(fixture)
    for key in (
        "schema_version",
        "status",
        "theorem_authority_pr",
        "research_anchor_pr",
        "routing_sync_pr",
        "source_schedule_schema_version",
        "source_fixture_schema_version",
        "primary_box_count",
        "control_box_count",
    ):
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#185 schedule mismatch: {key}")

    actual = schedule.get("boxes")
    wanted = expected["boxes"]
    if not isinstance(actual, list) or len(actual) != len(wanted):
        raise AssertionError("post-#185 schedule box count mismatch")
    expected_by_label = {b["label"]: b for b in wanted}
    labels = [b.get("label") for b in actual]
    if len(set(labels)) != len(labels) or set(labels) != set(expected_by_label):
        raise AssertionError("post-#185 schedule label mismatch")
    keys = (
        "label", "Q", "role", "primary", "side", "offset_bit", "radius_bit",
        "center_num", "lo_num", "hi_num", "den",
    )
    for box in actual:
        exp = expected_by_label[box["label"]]
        for key in keys:
            if box.get(key) != exp.get(key):
                raise AssertionError(f"post-#185 schedule drift for {box['label']} field {key}")


def _assert_consistent(label: str, dec: dict, require_h1: bool) -> None:
    if require_h1 and not dec["h1_certified"]:
        raise AssertionError(f"expected primary exact-center H1 regression: {label}")
    if not dec["h1_certified"]:
        return
    for key in (
        "remainder_direct_residual_overlap",
        "full_decomposition_overlap",
        "ratio_margin_identity_overlap",
        "existing_schur_pivot_derivative_overlap",
    ):
        if not dec.get(key, False):
            raise AssertionError(f"rigorous remainder-drift consistency failure {key}: {label}")


def _serialize_decomposition(dec: dict) -> dict:
    if not dec["h1_certified"]:
        return {
            "h1_certified": False,
            "scope": dec["scope"],
        }
    fields = (
        "W_norm_sq",
        "c_norm_sq",
        "x",
        "envelope_norm_sq",
        "a_remainder_prime",
        "b_remainder_prime",
        "d_remainder_prime",
        "universal_log_drift_L",
        "remainder_envelope_derivative_L",
        "remainder_envelope_derivative_residual_L",
        "full_pivot_derivative_L",
        "reconstructed_full_pivot_derivative_L",
        "domination_margin_L",
        "normalized_ratio",
        "ratio_gap_to_one",
        "scaled_margin",
    )
    out = {
        "h1_certified": True,
        "scope": dec["scope"],
        **{field: ball_record(dec[field]) for field in fields},
        "margin_sign": dec["margin_sign"],
        "ratio_vs_one": dec["ratio_vs_one"],
        "remainder_direct_residual_overlap": bool(dec["remainder_direct_residual_overlap"]),
        "full_decomposition_overlap": bool(dec["full_decomposition_overlap"]),
        "ratio_margin_identity_overlap": bool(dec["ratio_margin_identity_overlap"]),
        "existing_schur_pivot_derivative_overlap": bool(dec["existing_schur_pivot_derivative_overlap"]),
    }
    return out


def _record(box: dict, fixture: dict) -> dict:
    point = point_remainder_drift_record(box)
    interval = interval_remainder_drift_record(box)
    require_h1 = bool(
        fixture["require_primary_exact_center_h1"]
        and box["primary"]
        and box["role"] == "side"
    )
    _assert_consistent(box["label"] + ":point", point["decomposition"], require_h1)
    _assert_consistent(box["label"] + ":box", interval["decomposition"], False)

    point_even = point["base"]["record"]["even"]
    interval_rec = interval["base"]["record"]
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
            "L": ball_record(point["base"]["L"]),
            "a": ball_record(point_even["a"]),
            "b": ball_record(point_even["b"]),
            "d": ball_record(point_even["d"]),
            "a_prime": ball_record(point_even["a_prime"]),
            "b_prime": ball_record(point_even["b_prime"]),
            "d_prime": ball_record(point_even["d_prime"]),
            "decomposition": _serialize_decomposition(point["decomposition"]),
        },
        "interval": {
            "lo_num": int(box["lo_num"]),
            "hi_num": int(box["hi_num"]),
            "den": int(box["den"]),
            "L": ball_record(interval["base"]["L"]),
            "decomposition": _serialize_decomposition(interval["decomposition"]),
        },
        "odd_N2_predecessor": ball_record(interval_rec["odd_N2_predecessor"]),
        "odd_N2_predecessor_sign": sign_class(interval_rec["odd_N2_predecessor"]),
    }


def _classify(records: list[dict]) -> dict:
    primary = [r for r in records if r["primary"] and r["role"] == "side"]
    if not primary:
        raise AssertionError("no primary side states in frozen schedule")

    positive = []
    negative = []
    unresolved = []
    ratio_lt = []
    ratio_gt = []
    ratio_unresolved = []
    for rec in primary:
        dec = rec["exact_center"]["decomposition"]
        if not dec["h1_certified"]:
            unresolved.append(rec["label"])
            ratio_unresolved.append(rec["label"])
            continue
        sign = dec["margin_sign"]
        if sign == "POSITIVE_CERTIFIED":
            positive.append(rec["label"])
        elif sign == "NEGATIVE_CERTIFIED":
            negative.append(rec["label"])
        else:
            unresolved.append(rec["label"])

        ratio = dec["ratio_vs_one"]
        if ratio == "LT_ONE_CERTIFIED":
            ratio_lt.append(rec["label"])
        elif ratio == "GT_ONE_CERTIFIED":
            ratio_gt.append(rec["label"])
        else:
            ratio_unresolved.append(rec["label"])

    if len(positive) == len(primary):
        disposition = "DOMINATION_SIGNAL_STRONG"
    elif positive and negative:
        disposition = "DOMINATION_SIGNAL_MIXED"
    elif negative:
        disposition = "DOMINATION_SIGNAL_FAILS"
    else:
        disposition = "DOMINATION_SIGNAL_UNRESOLVED"

    interval_applicable = [
        r for r in primary
        if r["interval"]["decomposition"]["h1_certified"]
    ]
    if not interval_applicable:
        finite_width_scope = "FINITE_WIDTH_OUT_OF_H1_SCOPE"
    else:
        finite_width_scope = "FINITE_WIDTH_PARTIALLY_IN_H1_SCOPE"

    return {
        "disposition": disposition,
        "primary_count": len(primary),
        "positive_margin_labels": positive,
        "negative_margin_labels": negative,
        "unresolved_margin_labels": unresolved,
        "ratio_lt_one_labels": ratio_lt,
        "ratio_gt_one_labels": ratio_gt,
        "ratio_unresolved_labels": ratio_unresolved,
        "finite_width_scope": finite_width_scope,
        "finite_width_applicable_primary_count": len(interval_applicable),
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST185_Q14_REMAINDER_DRIFT_CERTIFICATE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)
    set_precision(int(fixture["arb_precision_bits"]))

    records = [_record(box, fixture) for box in schedule["boxes"]]
    disposition = _classify(records)
    if disposition["disposition"] not in fixture["research_dispositions"]:
        raise AssertionError("unknown research disposition")

    out = {
        "schema_version": "POST185_FB05_Q13_REMAINDER_DRIFT_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "selected_target": fixture["selected_target"],
        "records": records,
        "research_disposition": disposition,
        "nonclaims": fixture["nonclaims"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "disposition": disposition["disposition"],
        "positive_margin_labels": disposition["positive_margin_labels"],
        "negative_margin_labels": disposition["negative_margin_labels"],
        "unresolved_margin_labels": disposition["unresolved_margin_labels"],
        "finite_width_scope": disposition["finite_width_scope"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
