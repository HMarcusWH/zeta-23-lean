#!/usr/bin/env python3
"""Certify the frozen post-#194 A/B/C Q14 trajectory enclosure audit."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import (
    GLOBAL_MONOTONE_ORIENTATION,
    J_POSITIVE,
)
from post194_fb05_q14_parity_trajectory_sharp_enclosure import (
    audit_sharp_parity_trajectory,
)
from probe_post194_fb05_q14_parity_trajectory_sharp_enclosure_scope import (
    sharp_trajectory_schedule,
)

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post194_fb05_q14_parity_trajectory_sharp_enclosure_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = sharp_trajectory_schedule(fixture)
    keys = (
        "schema_version",
        "status",
        "claim_cap",
        "base_main_sha",
        "base_main_tree",
        "theorem_authority_pr",
        "research_authority_pr",
        "routing_sync_pr",
        "selected_target",
        "required_ancestry_control",
        "arb_precision_bits",
        "max_refinement_depth",
        "max_evaluated_cells",
        "boxes",
        "primary_box_count",
        "control_box_count",
        "primary_hull",
        "policy",
    )
    for key in keys:
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#194 sharp schedule drift: {key}")


def _coverage_fraction(localization: dict) -> tuple[str, str, str]:
    hull = localization["hull"]
    hull_width = Fraction(
        int(hull["hi_num"]) - int(hull["lo_num"]), int(hull["den"])
    )
    unresolved_width = sum(
        (
            Fraction(
                int(span["hi_num"]) - int(span["lo_num"]),
                int(span["den"]),
            )
            for span in localization["unresolved_spans"]
        ),
        Fraction(0, 1),
    )
    certified_fraction = Fraction(1, 1) - unresolved_width / hull_width
    return str(hull_width), str(unresolved_width), str(certified_fraction)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST194_FB05_Q14_PARITY_TRAJECTORY_SHARP_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)

    result = audit_sharp_parity_trajectory(
        schedule,
        precision_bits=int(fixture["arb_precision_bits"]),
        max_depth=int(fixture["max_refinement_depth"]),
        max_cells=int(fixture["max_evaluated_cells"]),
    )
    if result["status"] != "PASS":
        raise AssertionError("sharp parity trajectory audit did not execute cleanly")
    if result["synthetic_second_order_controls"]["status"] != "PASS":
        raise AssertionError("second-order synthetic controls failed")

    baseline = result["baseline_post193"]["localization"]
    expected_baseline = fixture["expected_post193_baseline"]
    if baseline["classification"] != expected_baseline["classification"]:
        raise AssertionError("post-#193 baseline classification failed to replay")
    if int(baseline["evaluated_cell_count"]) != int(expected_baseline["evaluated_cell_count"]):
        raise AssertionError("post-#193 baseline evaluated-cell count failed to replay")
    if baseline["evaluated_orientation_counts"] != expected_baseline["evaluated_orientation_counts"]:
        raise AssertionError("post-#193 baseline orientation counts failed to replay")
    if not result["baseline_post193"]["all_inherited_P1_P2_crosschecks_pass"]:
        raise AssertionError("post-#193 inherited P1/P2/J crosschecks regressed")

    sharp = result["sharp_localization"]
    classification = sharp["classification"]
    if classification not in fixture["permitted_classifications"]:
        raise AssertionError(f"unexpected sharp trajectory classification: {classification}")
    if sharp["representation_conflict_count"] != 0:
        raise AssertionError("equivalent sharp trajectory representations conflict")
    if sharp["evaluated_cell_count"] > int(fixture["max_evaluated_cells"]):
        raise AssertionError("sharp trajectory exceeded frozen cell budget")
    if sharp["leaf_count"] < 1:
        raise AssertionError("sharp trajectory produced empty leaf cover")

    if result["theorem_promotion"] or result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("post-#194 trajectory claim firewall regression")

    hull_width, unresolved_width, certified_fraction = _coverage_fraction(sharp)
    global_positive_hull = (
        classification == GLOBAL_MONOTONE_ORIENTATION
        and sharp["uniform_orientation"] == J_POSITIVE
        and sharp["unresolved_span_count"] == 0
    )
    bounded_twin_exclusion = bool(
        sharp["distinct_aperture_twin_excluded_outside_reported_fold_region"]
    )

    out = {
        "schema_version": "POST194_FB05_Q14_PARITY_TRAJECTORY_SHARP_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "provenance": {
            "base_main_sha": fixture["base_main_sha"],
            "base_main_tree": fixture["base_main_tree"],
            "theorem_authority_pr": fixture["theorem_authority_pr"],
            "research_authority_pr": fixture["research_authority_pr"],
            "routing_sync_pr": fixture["routing_sync_pr"],
        },
        "result": result,
        "comparison": {
            "post193_baseline_classification": baseline["classification"],
            "post193_baseline_counts": baseline["evaluated_orientation_counts"],
            "sharp_classification": classification,
            "sharp_uniform_orientation": sharp["uniform_orientation"],
            "sharp_counts": sharp["evaluated_orientation_counts"],
            "method_orientation_counts": sharp["method_orientation_counts"],
            "second_order_h1_recovery_count": sharp["second_order_h1_recovery_count"],
            "representation_conflict_count": sharp["representation_conflict_count"],
            "hull_t_width": hull_width,
            "unresolved_t_width": unresolved_width,
            "certified_t_fraction": certified_fraction,
            "global_positive_hull": global_positive_hull,
            "bounded_distinct_aperture_twin_exclusion": bounded_twin_exclusion,
        },
        "interpretation": {
            "if_global_positive": (
                "DERIVED finite scope only: on this frozen Q14 branch, J>0 implies "
                "P2>0 and P1'>0, hence P1 is strictly increasing and distinct "
                "apertures cannot share P1 or the complete frozen seven-vector."
            ),
            "if_unresolved": (
                "Diagnose which of H1, direct log-slope, or transported-J remains "
                "dependency-limited. Do not increase the frozen budget or infer "
                "nonexistence from nonresolution."
            ),
        },
        "nonclaims": fixture["nonclaims"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")

    print(
        json.dumps(
            {
                "status": "PASS",
                "baseline_classification": baseline["classification"],
                "baseline_counts": baseline["evaluated_orientation_counts"],
                "classification": classification,
                "uniform_orientation": sharp["uniform_orientation"],
                "evaluated_cell_count": sharp["evaluated_cell_count"],
                "leaf_count": sharp["leaf_count"],
                "sharp_counts": sharp["evaluated_orientation_counts"],
                "method_orientation_counts": sharp["method_orientation_counts"],
                "second_order_h1_recovery_count": sharp["second_order_h1_recovery_count"],
                "representation_conflict_count": sharp["representation_conflict_count"],
                "unresolved_span_count": sharp["unresolved_span_count"],
                "certified_t_fraction": certified_fraction,
                "global_positive_hull": global_positive_hull,
                "bounded_distinct_aperture_twin_exclusion": bounded_twin_exclusion,
                "theorem_promotion": False,
                "fb05_closed": False,
                "negative_root_exclusion": False,
                "rh_claim": False,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
