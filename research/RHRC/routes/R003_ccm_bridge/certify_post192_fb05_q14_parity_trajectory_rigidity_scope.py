#!/usr/bin/env python3
"""Certify the frozen post-#192 Q14 parity-trajectory audit."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import (
    GLOBAL_MONOTONE_ORIENTATION,
    SINGLE_FOLD_REGION_LOCALIZED,
    audit_parity_trajectory,
)
from probe_post192_fb05_q14_parity_trajectory_rigidity_scope import parity_trajectory_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post192_fb05_q14_parity_trajectory_rigidity_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = parity_trajectory_schedule(fixture)
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
            raise AssertionError(f"post-#192 trajectory schedule drift: {key}")


def _span_width(span: dict) -> str:
    return str(Fraction(int(span["hi_num"]) - int(span["lo_num"]), int(span["den"])))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST192_FB05_Q14_PARITY_TRAJECTORY_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)

    result = audit_parity_trajectory(
        schedule,
        precision_bits=int(fixture["arb_precision_bits"]),
        max_depth=int(fixture["max_refinement_depth"]),
        max_cells=int(fixture["max_evaluated_cells"]),
    )
    if result["status"] != "PASS":
        raise AssertionError("parity trajectory audit did not execute cleanly")
    if not result["all_inherited_P1_P2_crosschecks_pass"]:
        raise AssertionError("reconstructed P1/P2/J graph disagrees with inherited #188 selectors")
    if result["synthetic_orientation_controls"]["status"] != "PASS":
        raise AssertionError("synthetic Wronskian orientation control failed")

    localization = result["localization"]
    classification = localization["classification"]
    if classification not in fixture["permitted_classifications"]:
        raise AssertionError(f"unexpected trajectory classification: {classification}")
    if localization["leaf_count"] < 1:
        raise AssertionError("empty trajectory leaf cover")
    if localization["evaluated_cell_count"] > int(fixture["max_evaluated_cells"]):
        raise AssertionError("trajectory evaluator exceeded frozen cell budget")

    exclusion = bool(localization["distinct_aperture_twin_excluded_outside_reported_fold_region"])
    if exclusion and classification not in (GLOBAL_MONOTONE_ORIENTATION, SINGLE_FOLD_REGION_LOCALIZED):
        raise AssertionError("trajectory twin exclusion overclaimed outside supported classification")

    if result["theorem_promotion"] or result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("trajectory claim firewall regression")

    unresolved_spans = localization["unresolved_spans"]
    hull = localization["hull"]
    hull_width = Fraction(int(hull["hi_num"]) - int(hull["lo_num"]), int(hull["den"]))
    unresolved_width = sum(
        (Fraction(int(span["hi_num"]) - int(span["lo_num"]), int(span["den"])) for span in unresolved_spans),
        Fraction(0, 1),
    )
    certified_fraction = Fraction(1, 1) - unresolved_width / hull_width

    out = {
        "schema_version": "POST192_FB05_Q14_PARITY_TRAJECTORY_RIGIDITY_CERTIFICATE_v1",
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
        "coverage_diagnostic": {
            "hull_t_width": str(hull_width),
            "unresolved_t_width": str(unresolved_width),
            "certified_t_fraction": str(certified_fraction),
            "note": "Coverage diagnostic only; not a probability, confidence level, or theorem-strength score."
        },
        "interpretation": {
            "classification": classification,
            "derived_distinct_aperture_twin_exclusion_outside_fold": exclusion,
            "next_question_if_single_fold": "Can J be shown to have exactly one nondegenerate zero inside the reported fold interval using J', P2', second derivatives, centered Taylor, or interval Newton?",
            "fallback_if_unresolved": "Non-resolution after the frozen budget remains an open trajectory-rigidity problem; do not infer twin nonexistence."
        },
        "nonclaims": fixture["nonclaims"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")

    print(json.dumps({
        "status": "PASS",
        "classification": classification,
        "evaluated_cell_count": localization["evaluated_cell_count"],
        "leaf_count": localization["leaf_count"],
        "orientation_sequence": localization["compressed_certified_orientation_sequence"],
        "unresolved_span_count": localization["unresolved_span_count"],
        "unresolved_span_widths": [_span_width(span) for span in unresolved_spans],
        "certified_t_fraction": str(certified_fraction),
        "distinct_aperture_twin_excluded_outside_fold": exclusion,
        "P1_P2_crosschecks": result["all_inherited_P1_P2_crosschecks_pass"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
