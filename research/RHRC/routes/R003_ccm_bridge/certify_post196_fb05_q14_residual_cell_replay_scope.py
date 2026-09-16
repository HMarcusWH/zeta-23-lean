#!/usr/bin/env python3
"""Certify the post-#196 replay of the unique unevaluated #195 budget leaf."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import (
    GLOBAL_MONOTONE_ORIENTATION,
    J_NEGATIVE,
    J_POSITIVE,
)
from post196_fb05_q14_residual_cell_replay import replay_post195_budget_leaf
from probe_post196_fb05_q14_residual_cell_replay_scope import residual_replay_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post196_fb05_q14_residual_cell_replay_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = residual_replay_schedule(fixture)
    for key in (
        "schema_version",
        "status",
        "claim_cap",
        "base_main_sha",
        "base_main_tree",
        "theorem_authority_pr",
        "research_authority_pr",
        "routing_sync_pr",
        "inherited_post195_schedule_schema",
        "selected_target",
        "required_ancestry_control",
        "arb_precision_bits",
        "max_refinement_depth",
        "max_evaluated_cells",
        "followup_evaluated_cells",
        "boxes",
        "primary_box_count",
        "control_box_count",
        "primary_hull",
        "policy",
    ):
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#196 residual replay schedule drift: {key}")


def _fractional_width(row: dict) -> Fraction:
    return Fraction(int(row["hi_num"]) - int(row["lo_num"]), int(row["den"]))


def _coverage_fraction(completed: dict) -> tuple[str, str, str]:
    hull_width = _fractional_width(completed["hull"])
    unresolved_width = sum((_fractional_width(span) for span in completed["unresolved_spans"]), Fraction(0, 1))
    return str(hull_width), str(unresolved_width), str(Fraction(1, 1) - unresolved_width / hull_width)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST196_FB05_Q14_RESIDUAL_CELL_REPLAY_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)

    result = replay_post195_budget_leaf(
        schedule,
        precision_bits=int(fixture["arb_precision_bits"]),
        max_depth=int(fixture["max_refinement_depth"]),
        max_cells=int(fixture["max_evaluated_cells"]),
    )
    if result["status"] != "PASS":
        raise AssertionError("residual-cell replay did not execute cleanly")

    sharp = result["post195_audit"]["sharp_localization"]
    expected = fixture["expected_post195_disposition"]
    exact_checks = {
        "classification": sharp["classification"],
        "evaluated_cell_count": int(sharp["evaluated_cell_count"]),
        "leaf_count": int(sharp["leaf_count"]),
        "evaluated_orientation_counts": sharp["evaluated_orientation_counts"],
        "second_order_h1_recovery_count": int(sharp["second_order_h1_recovery_count"]),
        "budget_exhausted_leaf_count": int(sharp["budget_exhausted_leaf_count"]),
        "representation_conflict_count": int(sharp["representation_conflict_count"]),
        "unresolved_span_count": int(sharp["unresolved_span_count"]),
    }
    for key, actual in exact_checks.items():
        if actual != expected[key]:
            raise AssertionError(f"post-#195 frozen disposition failed to replay: {key}")

    budget_leaf = result["residual_budget_leaf"]
    hull = sharp["hull"]
    budget_fraction = _fractional_width(budget_leaf) / _fractional_width(hull)
    if str(budget_fraction) != fixture["expected_budget_leaf_fraction_of_hull"]:
        raise AssertionError("post-#195 residual budget leaf width drift")
    if int(result["followup_evaluated_cell_count"]) != 1:
        raise AssertionError("residual replay evaluated more than one follow-up cell")
    if bool(result["recursive_followup_subdivision"]):
        raise AssertionError("residual replay recursively subdivided the follow-up cell")

    replayed = result["replayed_cell"]
    if replayed["orientation"] not in fixture["permitted_replayed_orientations"]:
        raise AssertionError(f"unexpected residual-cell orientation: {replayed['orientation']}")
    if replayed.get("representation_conflict"):
        raise AssertionError("residual cell has an A/B/C representation conflict")

    completed = result["completed_cover"]
    if completed["classification"] not in fixture["permitted_classifications"]:
        raise AssertionError(f"unexpected completed-cover classification: {completed['classification']}")
    if int(completed["leaf_count"]) != int(sharp["leaf_count"]):
        raise AssertionError("one-cell replay changed the inherited leaf partition")

    if result["theorem_promotion"] or result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("post-#196 residual replay claim firewall regression")

    hull_width, unresolved_width, certified_fraction = _coverage_fraction(completed)
    full_hull_signed_monotonicity = (
        completed["classification"] == GLOBAL_MONOTONE_ORIENTATION
        and completed["uniform_orientation"] in (J_POSITIVE, J_NEGATIVE)
        and completed["unresolved_span_count"] == 0
    )
    global_positive_hull = full_hull_signed_monotonicity and completed["uniform_orientation"] == J_POSITIVE
    bounded_twin_exclusion = bool(full_hull_signed_monotonicity)

    out = {
        "schema_version": "POST196_FB05_Q14_RESIDUAL_CELL_REPLAY_CERTIFICATE_v1",
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
            "post195_classification": sharp["classification"],
            "post195_evaluated_cell_count": sharp["evaluated_cell_count"],
            "post195_leaf_count": sharp["leaf_count"],
            "post195_counts": sharp["evaluated_orientation_counts"],
            "post195_budget_exhausted_leaf_count": sharp["budget_exhausted_leaf_count"],
            "budget_leaf_fraction_of_hull": str(budget_fraction),
            "followup_evaluated_cell_count": result["followup_evaluated_cell_count"],
            "replayed_cell_orientation": replayed["orientation"],
            "replayed_method_orientations": {
                "A": replayed["method_A_orientation"],
                "B": replayed["method_B_orientation"],
                "C": replayed["method_C_orientation"],
            },
            "completed_classification": completed["classification"],
            "completed_uniform_orientation": completed["uniform_orientation"],
            "completed_unresolved_span_count": completed["unresolved_span_count"],
            "hull_t_width": hull_width,
            "unresolved_t_width": unresolved_width,
            "certified_t_fraction": certified_fraction,
            "full_hull_signed_monotonicity": full_hull_signed_monotonicity,
            "global_positive_hull": global_positive_hull,
            "bounded_distinct_aperture_twin_exclusion": bounded_twin_exclusion,
        },
        "interpretation": {
            "if_positive": (
                "DERIVED finite scope only: if the replayed residual cell is J_POSITIVE, "
                "the unchanged #195 leaf partition becomes a complete positive Q14 cover; "
                "then P2>0 and P1'>0 on this frozen branch, so P1 is strictly increasing."
            ),
            "if_unresolved": (
                "The previously skipped cell is now genuinely evaluated and remains unresolved; "
                "the next step is representation/mechanism sharpening, not a larger hidden budget."
            ),
            "if_negative": (
                "A certified negative residual cell would falsify full-hull positive orientation "
                "on this frozen branch and redirect the route to the local sign-change mechanism."
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

    print(json.dumps({
        "status": "PASS",
        "post195_classification": sharp["classification"],
        "post195_evaluated_cell_count": sharp["evaluated_cell_count"],
        "post195_leaf_count": sharp["leaf_count"],
        "post195_budget_exhausted_leaf_count": sharp["budget_exhausted_leaf_count"],
        "budget_leaf_fraction_of_hull": str(budget_fraction),
        "followup_evaluated_cell_count": result["followup_evaluated_cell_count"],
        "replayed_cell_orientation": replayed["orientation"],
        "replayed_method_orientations": {
            "A": replayed["method_A_orientation"],
            "B": replayed["method_B_orientation"],
            "C": replayed["method_C_orientation"],
        },
        "completed_classification": completed["classification"],
        "completed_uniform_orientation": completed["uniform_orientation"],
        "completed_unresolved_span_count": completed["unresolved_span_count"],
        "certified_t_fraction": certified_fraction,
        "full_hull_signed_monotonicity": full_hull_signed_monotonicity,
        "global_positive_hull": global_positive_hull,
        "bounded_distinct_aperture_twin_exclusion": bounded_twin_exclusion,
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
