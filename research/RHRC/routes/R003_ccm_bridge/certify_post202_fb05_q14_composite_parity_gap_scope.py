#!/usr/bin/env python3
"""Certify the post-#202 full-composite parity-gap mechanism audit."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import GLOBAL_MONOTONE_ORIENTATION, J_POSITIVE
from post196_fb05_q14_residual_cell_replay import replay_post195_budget_leaf
from post200_fb05_q14_discrepancy_mechanism import audit_discrepancy_mechanism
from post202_fb05_q14_composite_parity_gap_mechanism import audit_composite_parity_gap
from probe_post196_fb05_q14_residual_cell_replay_scope import residual_replay_schedule
from probe_post200_fb05_q14_discrepancy_mechanism_scope import discrepancy_schedule
from probe_post202_fb05_q14_composite_parity_gap_scope import composite_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post202_fb05_q14_composite_parity_gap_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = composite_schedule(fixture)
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
        "center_kill_switch_pattern",
        "policy",
    ):
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#202 composite schedule drift: {key}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST202_FB05_Q14_COMPOSITE_PARITY_GAP_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)

    post201_fixture = json.loads(
        (HERE / "fixtures" / fixture["inherited_post201_fixture"]).read_text(encoding="utf-8")
    )
    post199_fixture = json.loads(
        (HERE / "fixtures" / post201_fixture["inherited_post199_fixture"]).read_text(encoding="utf-8")
    )
    post197_fixture = json.loads(
        (HERE / "fixtures" / post199_fixture["inherited_post197_fixture"]).read_text(encoding="utf-8")
    )
    inherited_schedule = residual_replay_schedule(post197_fixture)
    if inherited_schedule["boxes"] != schedule["boxes"]:
        raise AssertionError("composite schedule no longer matches exact post-#197 box ancestry")
    if inherited_schedule["primary_hull"] != schedule["primary_hull"]:
        raise AssertionError("composite schedule no longer matches exact post-#197 primary hull")

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
        raise AssertionError("composite audit requires exact completed positive Q14 cover")

    # Re-run the immediately preceding research representation before changing level.
    post201_schedule = discrepancy_schedule(post201_fixture)
    inherited201 = audit_discrepancy_mechanism(
        post201_schedule,
        completed,
        precision_bits=int(fixture["arb_precision_bits"]),
    )
    expected201 = fixture["expected_post201"]
    if inherited201["mechanism_classification"] != expected201["mechanism_classification"]:
        raise AssertionError("post-#201 mechanism disposition failed to replay")
    if int(inherited201["summary"]["positive_source_sum_leaf_count"]) != int(expected201["positive_source_sum_leaf_count"]):
        raise AssertionError("post-#201 positive paired-source count failed to replay")
    if int(inherited201["summary"]["unresolved_source_sum_leaf_count"]) != int(expected201["unresolved_source_sum_leaf_count"]):
        raise AssertionError("post-#201 unresolved paired-source count failed to replay")
    if inherited201["control_transfer_status"] != expected201["control_transfer_status"]:
        raise AssertionError("post-#201 control transfer status failed to replay")

    result = audit_composite_parity_gap(
        schedule,
        completed,
        precision_bits=int(fixture["arb_precision_bits"]),
    )
    if result["status"] != "PASS":
        raise AssertionError("composite parity-gap audit did not execute cleanly")
    if result["mechanism_classification"] not in fixture["permitted_mechanism_classifications"]:
        raise AssertionError(f"unexpected composite classification: {result['mechanism_classification']}")
    if result["control_transfer_status"] not in fixture["permitted_control_transfer_statuses"]:
        raise AssertionError(f"unexpected composite control status: {result['control_transfer_status']}")

    gate_survives = bool(result["center_kill_switch"]["survives"])
    if gate_survives:
        if not result["full_cover_executed"]:
            raise AssertionError("surviving center gate did not execute the inherited full cover")
        if int(result["completed_leaf_count"]) != int(expected197["leaf_count"]):
            raise AssertionError("composite audit changed the inherited leaf partition")
        for row in result["primary_cells"]:
            checks = row["checks"]
            required = (
                all(checks["center_gap_reconstruction"].values()),
                all(checks["interval_gap_reconstruction"].values()),
                checks["gap_transport_direct_method_c_overlap"],
                checks["factor_sum_gap_transport_overlap"],
                checks["scalar_cancellation_before_interval_transport"],
                row["direct_method_c_positive"],
            )
            if not all(required):
                raise AssertionError("composite reconstruction invariant failed")
    else:
        if result["full_cover_executed"] or result["primary_cells"]:
            raise AssertionError("failed center kill-switch was improperly rescued by full-cover execution")
        if int(result["completed_leaf_count"]) != 0:
            raise AssertionError("failed center gate must report zero full-cover leaves")

    if result["theorem_promotion"] or result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("composite mechanism claim firewall regression")

    out = {
        "schema_version": "POST202_FB05_Q14_COMPOSITE_PARITY_GAP_CERTIFICATE_v1",
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
        "post201_replay": {
            "mechanism_classification": inherited201["mechanism_classification"],
            "positive_source_sum_leaf_count": inherited201["summary"]["positive_source_sum_leaf_count"],
            "unresolved_source_sum_leaf_count": inherited201["summary"]["unresolved_source_sum_leaf_count"],
            "control_transfer_status": inherited201["control_transfer_status"],
        },
        "result": result,
        "interpretation": {
            "pattern_falsified": "The predeclared simple factor-sign mechanism failed before full-cover execution; do not rescue it by fitting a new sign pattern.",
            "pattern_lock": "A full-cover sign lock is bounded Q14 research until generalized to arbitrary retained first-bad states and formalized.",
            "cooperative_lock": "Nonnegative composite factor terms can expose a bounded mechanism even when every primitive factor sign is not separately resolved.",
            "mixed_reconstructable": "The full-composite representation reconstructs positive J but does not isolate a uniform simple factor mechanism.",
            "dependency_unresolved": "If the full-composite transport loses sign resolution, Pair-A representation engineering is consumed and Pair D/Pair B should gain priority."
        },
        "nonclaims": fixture["nonclaims"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")

    summary = result["summary"] or {}
    print(json.dumps({
        "status": "PASS",
        "post197_classification": completed["classification"],
        "post197_uniform_orientation": completed["uniform_orientation"],
        "post201_mechanism_classification": inherited201["mechanism_classification"],
        "center_kill_switch_survives": gate_survives,
        "full_cover_executed": result["full_cover_executed"],
        "completed_leaf_count": result["completed_leaf_count"],
        "gap_positive_leaf_count": summary.get("gap_positive_leaf_count"),
        "gap_unresolved_leaf_count": summary.get("gap_unresolved_leaf_count"),
        "pattern_lock_leaf_count": summary.get("pattern_lock_leaf_count"),
        "cooperative_lock_leaf_count": summary.get("cooperative_lock_leaf_count"),
        "mechanism_classification": result["mechanism_classification"],
        "control_transfer_status": result["control_transfer_status"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
