#!/usr/bin/env python3
"""Certify the frozen post-#186 mixed-drift selector audit.

Green means faithful execution.  Strong/partial/fail/unresolved are all valid
research outcomes and do not promote theorem authority.  RH remains OPEN.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import arb

from canonical_source_arb import ball_record, set_precision
from post179_fb05_q13_correlation_preserving_derivative import sign_class
from post185_fb05_q13_remainder_drift import point_remainder_drift_record
from post187_fb05_q14_mixed_drift_selector import (
    normalization_invariance_record,
    selector_record_from_box,
)
from probe_post187_fb05_q14_mixed_drift_selector_scope import selector_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = selector_schedule(fixture)
    for key in (
        "schema_version", "status", "theorem_authority_pr", "research_anchor_pr",
        "routing_sync_pr", "source_schedule_schema_version", "source_fixture_schema_version",
        "primary_box_count", "control_box_count", "candidate_rule_ids", "target_labels_included",
    ):
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#187 schedule mismatch: {key}")
    if schedule.get("target_labels_included") is not False:
        raise AssertionError("selector probe leaked target labels")
    actual = schedule.get("boxes")
    wanted = expected["boxes"]
    if not isinstance(actual, list) or len(actual) != len(wanted):
        raise AssertionError("post-#187 schedule box count mismatch")
    wanted_by_label = {b["label"]: b for b in wanted}
    keys = (
        "label", "Q", "role", "primary", "side", "offset_bit", "radius_bit",
        "center_num", "lo_num", "hi_num", "den",
    )
    for box in actual:
        exp = wanted_by_label.get(box.get("label"))
        if exp is None:
            raise AssertionError(f"unknown selector schedule label: {box.get('label')}")
        for key in keys:
            if box.get(key) != exp.get(key):
                raise AssertionError(f"post-#187 schedule drift {box['label']} field {key}")


def _threshold(kind: str) -> arb:
    if kind == "ZERO":
        return arb(0)
    if kind == "ONE":
        return arb(1)
    raise AssertionError(f"unsupported threshold kind: {kind}")


def _relation(value, threshold_kind: str) -> str:
    if value is None:
        return "OUT_OF_CANDIDATE_SCOPE"
    sign = sign_class(value - _threshold(threshold_kind))
    if sign == "NEGATIVE_CERTIFIED":
        return "LT"
    if sign == "POSITIVE_CERTIFIED":
        return "GT"
    return "UNRESOLVED"


def _target(box: dict) -> dict:
    dec = point_remainder_drift_record(box)["decomposition"]
    if not dec["h1_certified"]:
        return {"scope": "OUT_OF_CERTIFIED_H1_SCOPE", "class": None}
    sign = dec["margin_sign"]
    if sign == "POSITIVE_CERTIFIED":
        cls = "POSITIVE_MARGIN"
    elif sign == "NEGATIVE_CERTIFIED":
        cls = "NEGATIVE_MARGIN"
    else:
        cls = "UNRESOLVED_MARGIN"
    return {"scope": "CERTIFIED_H1_SCOPE", "class": cls}


def _orientation_metrics(rows: list[dict], orientation: str) -> dict:
    tp = fp = tn = fn = unresolved = 0
    for row in rows:
        rel = row["relation"]
        target = row["target"]
        if rel not in ("LT", "GT") or target not in ("POSITIVE_MARGIN", "NEGATIVE_MARGIN"):
            unresolved += 1
            continue
        predicted_positive = rel == orientation
        actual_positive = target == "POSITIVE_MARGIN"
        if predicted_positive and actual_positive:
            tp += 1
        elif predicted_positive and not actual_positive:
            fp += 1
        elif not predicted_positive and actual_positive:
            fn += 1
        else:
            tn += 1
    return {
        "orientation": orientation,
        "true_positive": tp,
        "false_positive": fp,
        "true_negative": tn,
        "false_negative": fn,
        "unresolved": unresolved,
        "correct": tp + tn,
        "exact_split": unresolved == 0 and fp == 0 and fn == 0,
        "one_sided_survivor": unresolved == 0 and fp == 0 and tp >= 1,
    }


def _choose_orientation(rows: list[dict]) -> tuple[str | None, dict | None]:
    options = [_orientation_metrics(rows, "LT"), _orientation_metrics(rows, "GT")]
    exact = [m for m in options if m["exact_split"]]
    if exact:
        return exact[0]["orientation"], exact[0]
    options.sort(
        key=lambda m: (
            m["unresolved"] == 0,
            m["false_positive"] == 0,
            m["true_positive"],
            m["correct"],
            -m["false_positive"],
            -m["false_negative"],
        ),
        reverse=True,
    )
    best = options[0]
    if best["true_positive"] + best["true_negative"] == 0:
        return None, best
    return best["orientation"], best


def _primary_status(metrics: dict | None) -> str:
    if metrics is None or metrics["unresolved"]:
        return "PRIMARY_UNRESOLVED"
    if metrics["exact_split"]:
        return "EXACT_PRIMARY_SPLIT"
    if metrics["one_sided_survivor"]:
        return "ONE_SIDED_PRIMARY_SURVIVOR"
    return "PRIMARY_CONTRADICTION"


def _holdout_eval(row: dict, orientation: str | None) -> str:
    if row["target_scope"] != "CERTIFIED_H1_SCOPE":
        return "HOLDOUT_OUT_OF_H1_SCOPE"
    if row["relation"] not in ("LT", "GT") or row["target"] == "UNRESOLVED_MARGIN":
        return "HOLDOUT_CANDIDATE_UNRESOLVED"
    if orientation is None:
        return "HOLDOUT_CANDIDATE_UNRESOLVED"
    predicted_positive = row["relation"] == orientation
    actual_positive = row["target"] == "POSITIVE_MARGIN"
    return "HOLDOUT_CORRECT" if predicted_positive == actual_positive else "HOLDOUT_CONTRADICTION"


def _candidate_result(rule: dict, records: list[dict]) -> dict:
    primary = [r for r in records if r["primary"] and r["role"] == "side"]
    primary_rows = []
    for rec in primary:
        value = rec["selector"]["candidates"].get(rule["field"])
        primary_rows.append({
            "label": rec["label"],
            "relation": _relation(value, rule["threshold_kind"]),
            "target": rec["target"]["class"],
        })
    orientation, metrics = _choose_orientation(primary_rows)
    status = _primary_status(metrics)

    holdouts = []
    for rec in records:
        if rec["primary"]:
            continue
        value = rec["selector"]["candidates"].get(rule["field"])
        row = {
            "label": rec["label"],
            "Q": rec["Q"],
            "role": rec["role"],
            "relation": _relation(value, rule["threshold_kind"]),
            "target_scope": rec["target"]["scope"],
            "target": rec["target"]["class"],
        }
        row["outcome"] = _holdout_eval(row, orientation)
        holdouts.append(row)

    same_q = [h for h in holdouts if h["Q"] == 14]
    transport = [h for h in holdouts if h["Q"] != 14]
    same_q_resolved = [h for h in same_q if h["outcome"] in ("HOLDOUT_CORRECT", "HOLDOUT_CONTRADICTION")]
    transport_resolved = [h for h in transport if h["outcome"] in ("HOLDOUT_CORRECT", "HOLDOUT_CONTRADICTION")]
    return {
        "id": rule["id"],
        "field": rule["field"],
        "candidate_class": rule["candidate_class"],
        "strong_eligible": bool(rule["strong_eligible"]),
        "threshold_kind": rule["threshold_kind"],
        "orientation_from_primary": orientation,
        "primary_status": status,
        "primary_metrics": metrics,
        "primary_rows": primary_rows,
        "same_q_holdout_resolved_count": len(same_q_resolved),
        "same_q_holdout_correct_count": sum(h["outcome"] == "HOLDOUT_CORRECT" for h in same_q_resolved),
        "same_q_holdout_contradiction_count": sum(h["outcome"] == "HOLDOUT_CONTRADICTION" for h in same_q_resolved),
        "transport_resolved_count": len(transport_resolved),
        "transport_correct_count": sum(h["outcome"] == "HOLDOUT_CORRECT" for h in transport_resolved),
        "transport_contradiction_count": sum(h["outcome"] == "HOLDOUT_CONTRADICTION" for h in transport_resolved),
        "holdouts": holdouts,
    }


def _overall(candidate_results: list[dict]) -> dict:
    strong = [
        r for r in candidate_results
        if r["strong_eligible"]
        and r["primary_status"] == "EXACT_PRIMARY_SPLIT"
        and r["same_q_holdout_resolved_count"] >= 1
        and r["same_q_holdout_contradiction_count"] == 0
    ]
    partial = [
        r for r in candidate_results
        if r["primary_status"] in ("EXACT_PRIMARY_SPLIT", "ONE_SIDED_PRIMARY_SURVIVOR")
    ]
    unresolved = [r for r in candidate_results if r["primary_status"] == "PRIMARY_UNRESOLVED"]
    if strong:
        disposition = "SELECTOR_SIGNAL_STRONG"
    elif partial:
        disposition = "SELECTOR_SIGNAL_PARTIAL"
    elif unresolved:
        disposition = "SELECTOR_SIGNAL_UNRESOLVED"
    else:
        disposition = "SELECTOR_SIGNAL_FAILS"
    return {
        "disposition": disposition,
        "strong_candidate_ids": [r["id"] for r in strong],
        "partial_candidate_ids": [r["id"] for r in partial],
        "unresolved_candidate_ids": [r["id"] for r in unresolved],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }


def _serialize_selector(rec: dict) -> dict:
    return {
        "scope": rec["scope"],
        "candidates": {
            key: None if value is None else ball_record(value)
            for key, value in rec["candidates"].items()
        },
        "diagnostics": {
            key: ball_record(value)
            for key, value in rec["diagnostics"].items()
        },
        "checks": rec["checks"],
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST187_Q14_SELECTOR_CERTIFICATE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)
    set_precision(int(fixture["arb_precision_bits"]))

    records = []
    for box in schedule["boxes"]:
        selector = selector_record_from_box(box)
        target = _target(box)
        if box["primary"] and box["role"] == "side" and target["scope"] != "CERTIFIED_H1_SCOPE":
            raise AssertionError(f"primary target H1 regression: {box['label']}")
        if selector["scope"] == "CERTIFIED_H1_SCOPE":
            for key in ("channel_matrix_reconstruction_overlap", "channel_directional_sum_overlap"):
                if not selector["checks"].get(key, False):
                    raise AssertionError(f"selector consistency failure {key}: {box['label']}")
            inv = normalization_invariance_record(box, fixture["normalization_rescalings"])
            if not inv["all_overlap"]:
                raise AssertionError(f"selector normalization regression: {box['label']}")
        records.append({
            "label": box["label"],
            "Q": int(box["Q"]),
            "role": box["role"],
            "primary": bool(box["primary"]),
            "side": box.get("side"),
            "selector": selector,
            "target": target,
        })

    primary_targets = [r["target"]["class"] for r in records if r["primary"] and r["role"] == "side"]
    if not ("POSITIVE_MARGIN" in primary_targets and "NEGATIVE_MARGIN" in primary_targets):
        raise AssertionError("post-#186 mixed target regression")
    if any(t == "UNRESOLVED_MARGIN" for t in primary_targets):
        raise AssertionError("post-#186 primary target unexpectedly unresolved")

    candidate_results = [_candidate_result(rule, records) for rule in fixture["candidate_rules"]]
    overall = _overall(candidate_results)
    if overall["disposition"] not in fixture["selector_dispositions"]:
        raise AssertionError("unknown selector research disposition")

    out = {
        "schema_version": "POST187_FB05_Q14_MIXED_DRIFT_SELECTOR_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "theorem_authority_pr": fixture["theorem_authority_pr"],
        "research_anchor_pr": fixture["research_anchor_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "selected_target": fixture["selected_target"],
        "orientation_policy": fixture["orientation_policy"],
        "records": [
            {
                "label": r["label"], "Q": r["Q"], "role": r["role"],
                "primary": r["primary"], "side": r["side"],
                "selector": _serialize_selector(r["selector"]),
                "target": r["target"],
            }
            for r in records
        ],
        "candidate_results": candidate_results,
        "research_disposition": overall,
        "nonclaims": fixture["nonclaims"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")

    print(json.dumps({
        "status": "PASS",
        "disposition": overall["disposition"],
        "strong_candidate_ids": overall["strong_candidate_ids"],
        "partial_candidate_ids": overall["partial_candidate_ids"],
        "unresolved_candidate_ids": overall["unresolved_candidate_ids"],
        "candidate_table": [
            {
                "id": r["id"],
                "primary": r["primary_status"],
                "orientation": r["orientation_from_primary"],
                "q14_holdout": [r["same_q_holdout_correct_count"], r["same_q_holdout_contradiction_count"]],
                "transport": [r["transport_correct_count"], r["transport_contradiction_count"]],
            }
            for r in candidate_results
        ]
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
