#!/usr/bin/env python3
"""Certify the post-#200 cancellation-preserving discrepancy mechanism audit."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import GLOBAL_MONOTONE_ORIENTATION, J_POSITIVE
from post196_fb05_q14_residual_cell_replay import replay_post195_budget_leaf
from post198_fb05_q14_parity_source_mechanism import audit_source_mechanism
from post200_fb05_q14_discrepancy_mechanism import audit_discrepancy_mechanism
from probe_post196_fb05_q14_residual_cell_replay_scope import residual_replay_schedule
from probe_post200_fb05_q14_discrepancy_mechanism_scope import discrepancy_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post200_fb05_q14_discrepancy_mechanism_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = discrepancy_schedule(fixture)
    for key in (
        "schema_version",
        "status",
        "claim_cap",
        "base_main_sha",
        "base_main_tree",
        "theorem_authority_pr",
        "research_authority_pr",
        "research_authority_head_sha",
        "research_authority_merge_sha",
        "research_authority_tree_sha",
        "routing_sync_pr",
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
        "paired_channels",
        "policy",
    ):
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#200 discrepancy schedule drift: {key}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST200_FB05_Q14_DISCREPANCY_MECHANISM_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)

    post199_fixture = json.loads(
        (HERE / "fixtures" / fixture["inherited_post199_fixture"]).read_text(encoding="utf-8")
    )
    post197_fixture = json.loads(
        (HERE / "fixtures" / post199_fixture["inherited_post197_fixture"]).read_text(encoding="utf-8")
    )
    inherited_schedule = residual_replay_schedule(post197_fixture)
    if inherited_schedule["boxes"] != schedule["boxes"]:
        raise AssertionError("discrepancy schedule no longer matches exact post-#197 box ancestry")
    if inherited_schedule["primary_hull"] != schedule["primary_hull"]:
        raise AssertionError("discrepancy schedule no longer matches exact post-#197 primary hull")

    replay = replay_post195_budget_leaf(
        inherited_schedule,
        precision_bits=int(fixture["arb_precision_bits"]),
        max_depth=int(post197_fixture["max_refinement_depth"]),
        max_cells=int(post197_fixture["max_evaluated_cells"]),
    )
    completed = replay["completed_cover"]
    expected197 = fixture["expected_post197"]
    if completed["classification"] != expected197["classification"]:
        raise AssertionError("post-#197 classification failed to replay")
    if completed["uniform_orientation"] != expected197["uniform_orientation"]:
        raise AssertionError("post-#197 uniform orientation failed to replay")
    if int(completed["leaf_count"]) != int(expected197["leaf_count"]):
        raise AssertionError("post-#197 leaf count failed to replay")
    if int(completed["unresolved_span_count"]) != int(expected197["unresolved_span_count"]):
        raise AssertionError("post-#197 unresolved span count failed to replay")
    if completed["classification"] != GLOBAL_MONOTONE_ORIENTATION or completed["uniform_orientation"] != J_POSITIVE:
        raise AssertionError("discrepancy audit requires exact completed positive Q14 cover")

    # Re-run the immediately preceding mechanism state before changing representation.
    inherited199 = audit_source_mechanism(
        schedule,
        completed,
        precision_bits=int(fixture["arb_precision_bits"]),
    )
    expected199 = fixture["expected_post199"]
    if inherited199["mechanism_classification"] != expected199["mechanism_classification"]:
        raise AssertionError("post-#199 joint mechanism disposition failed to replay")
    if inherited199["four_way_summary"]["classification"] != expected199["four_way_classification"]:
        raise AssertionError("post-#199 four-way disposition failed to replay")
    if inherited199["collapsed_three_way_summary"]["classification"] != expected199["collapsed_three_way_classification"]:
        raise AssertionError("post-#199 collapsed disposition failed to replay")
    if inherited199["control_transfer_status"] != expected199["control_transfer_status"]:
        raise AssertionError("post-#199 control transfer status failed to replay")

    result = audit_discrepancy_mechanism(
        schedule,
        completed,
        precision_bits=int(fixture["arb_precision_bits"]),
    )
    if result["status"] != "PASS":
        raise AssertionError("discrepancy mechanism audit did not execute cleanly")
    if result["mechanism_classification"] not in fixture["permitted_mechanism_classifications"]:
        raise AssertionError(f"unexpected discrepancy classification: {result['mechanism_classification']}")
    if result["control_transfer_status"] not in fixture["permitted_control_transfer_statuses"]:
        raise AssertionError(f"unexpected control transfer status: {result['control_transfer_status']}")
    if int(result["completed_leaf_count"]) != int(expected197["leaf_count"]):
        raise AssertionError("discrepancy audit changed the inherited leaf partition")

    for row in result["primary_cells"] + result["control_rows"]:
        checks = row["checks"]
        required = (
            checks["paired_direct_transport_overlap"],
            checks["pairing_before_parity_restriction"],
            all(checks["center_inherited_four_way_reconstruction"].values()),
            all(checks["center_paired_reconstruction"].values()),
            all(checks["interval_inherited_four_way_reconstruction"].values()),
            all(checks["interval_paired_reconstruction"].values()),
        )
        if not all(required):
            raise AssertionError("discrepancy reconstruction invariant failed")

    if result["theorem_promotion"] or result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("discrepancy mechanism claim firewall regression")

    out = {
        "schema_version": "POST200_FB05_Q14_DISCREPANCY_MECHANISM_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "provenance": {
            "base_main_sha": fixture["base_main_sha"],
            "base_main_tree": fixture["base_main_tree"],
            "theorem_authority_pr": fixture["theorem_authority_pr"],
            "research_authority_pr": fixture["research_authority_pr"],
            "research_authority_head_sha": fixture["research_authority_head_sha"],
            "research_authority_merge_sha": fixture["research_authority_merge_sha"],
            "research_authority_tree_sha": fixture["research_authority_tree_sha"],
            "routing_sync_pr": fixture["routing_sync_pr"],
        },
        "post197_replay": {
            "classification": completed["classification"],
            "uniform_orientation": completed["uniform_orientation"],
            "leaf_count": completed["leaf_count"],
            "unresolved_span_count": completed["unresolved_span_count"],
        },
        "post199_replay": {
            "mechanism_classification": inherited199["mechanism_classification"],
            "four_way_classification": inherited199["four_way_summary"]["classification"],
            "collapsed_three_way_classification": inherited199["collapsed_three_way_summary"]["classification"],
            "control_transfer_status": inherited199["control_transfer_status"],
        },
        "result": result,
        "interpretation": {
            "uniform_lock": "A threshold-free uniform lock is theorem-shaped only inside the declared bounded scope until generalized and formalized.",
            "mixed_reconstructable": "If the paired source sum is rigorously positive but DD/DA/AA remain mixed, upstream pairing recovered information without isolating a one-group mechanism.",
            "dependency_unresolved": "If upstream pairing still loses the sign while direct Method C remains positive, stop further source chopping and seek a higher-level composite identity.",
            "local_only": "Failure on adjacent Q13/Q15 controls marks a selected Q14 lock local; it does not weaken the direct Q14 J>0 certificate."
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
        "post197_classification": completed["classification"],
        "post197_uniform_orientation": completed["uniform_orientation"],
        "post199_mechanism_classification": inherited199["mechanism_classification"],
        "completed_leaf_count": result["completed_leaf_count"],
        "paired_source_sum_positive_leaf_count": result["summary"]["positive_source_sum_leaf_count"],
        "paired_source_sum_unresolved_leaf_count": result["summary"]["unresolved_source_sum_leaf_count"],
        "mechanism_classification": result["mechanism_classification"],
        "selected_uniform_lock_group": result["selected_uniform_lock_group"],
        "control_transfer_status": result["control_transfer_status"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
