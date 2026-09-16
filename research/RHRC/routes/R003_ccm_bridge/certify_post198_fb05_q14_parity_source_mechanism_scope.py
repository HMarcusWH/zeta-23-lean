#!/usr/bin/env python3
"""Certify the post-#198 Q14 parity source-mechanism audit."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import GLOBAL_MONOTONE_ORIENTATION, J_POSITIVE
from post196_fb05_q14_residual_cell_replay import replay_post195_budget_leaf
from post198_fb05_q14_parity_source_mechanism import audit_source_mechanism
from probe_post196_fb05_q14_residual_cell_replay_scope import residual_replay_schedule
from probe_post198_fb05_q14_parity_source_mechanism_scope import mechanism_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post198_fb05_q14_parity_source_mechanism_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = mechanism_schedule(fixture)
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
        "four_way_channels",
        "collapsed_channels",
        "policy",
    ):
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"post-#198 mechanism schedule drift: {key}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path("/tmp/POST198_FB05_Q14_PARITY_SOURCE_MECHANISM_CERTIFICATE.json"))
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)

    inherited_fixture = json.loads((HERE / "fixtures" / fixture["inherited_post197_fixture"]).read_text(encoding="utf-8"))
    inherited_schedule = residual_replay_schedule(inherited_fixture)
    if inherited_schedule["boxes"] != schedule["boxes"] or inherited_schedule["primary_hull"] != schedule["primary_hull"]:
        raise AssertionError("mechanism schedule no longer matches exact post-#197 ancestry")

    replay = replay_post195_budget_leaf(
        inherited_schedule,
        precision_bits=int(fixture["arb_precision_bits"]),
        max_depth=int(inherited_fixture["max_refinement_depth"]),
        max_cells=int(inherited_fixture["max_evaluated_cells"]),
    )
    completed = replay["completed_cover"]
    expected = fixture["expected_post197"]
    if completed["classification"] != expected["classification"]:
        raise AssertionError("post-#197 classification failed to replay")
    if completed["uniform_orientation"] != expected["uniform_orientation"]:
        raise AssertionError("post-#197 uniform orientation failed to replay")
    if int(completed["leaf_count"]) != int(expected["leaf_count"]):
        raise AssertionError("post-#197 leaf count failed to replay")
    if int(completed["unresolved_span_count"]) != int(expected["unresolved_span_count"]):
        raise AssertionError("post-#197 unresolved span count failed to replay")
    if completed["classification"] != GLOBAL_MONOTONE_ORIENTATION or completed["uniform_orientation"] != J_POSITIVE:
        raise AssertionError("mechanism audit requires the exact completed positive Q14 cover")

    result = audit_source_mechanism(
        schedule,
        completed,
        precision_bits=int(fixture["arb_precision_bits"]),
    )
    if result["status"] != "PASS":
        raise AssertionError("source-mechanism audit did not execute cleanly")
    if result["mechanism_classification"] not in fixture["permitted_mechanism_classifications"]:
        raise AssertionError(f"unexpected mechanism classification: {result['mechanism_classification']}")
    if int(result["completed_leaf_count"]) != int(expected["leaf_count"]):
        raise AssertionError("mechanism audit changed the post-#197 leaf partition")

    for row in result["primary_cells"] + result["control_rows"]:
        checks = row["checks"]
        required = (
            checks["four_way_direct_transport_overlap"],
            checks["collapsed_direct_transport_overlap"],
            checks["four_way_collapsed_transport_overlap"],
            checks["scalar_shift_self_wronskian_contains_zero"],
            all(checks["center_matrix_reconstruction"].values()),
            all(checks["interval_matrix_reconstruction"].values()),
        )
        if not all(required):
            raise AssertionError("source-mechanism reconstruction invariant failed")

    if result["theorem_promotion"] or result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("source-mechanism claim firewall regression")

    out = {
        "schema_version": "POST198_FB05_Q14_PARITY_SOURCE_MECHANISM_CERTIFICATE_v1",
        "status": "PASS",
        "claim_cap": fixture["claim_cap"],
        "provenance": {
            "base_main_sha": fixture["base_main_sha"],
            "base_main_tree": fixture["base_main_tree"],
            "theorem_authority_pr": fixture["theorem_authority_pr"],
            "research_authority_pr": fixture["research_authority_pr"],
            "research_authority_head_sha": fixture["research_authority_head_sha"],
            "research_authority_merge_sha": fixture["research_authority_merge_sha"],
            "routing_sync_pr": fixture["routing_sync_pr"],
        },
        "post197_replay": {
            "classification": completed["classification"],
            "uniform_orientation": completed["uniform_orientation"],
            "leaf_count": completed["leaf_count"],
            "unresolved_span_count": completed["unresolved_span_count"],
        },
        "result": result,
        "interpretation": {
            "uniform_lock": "A rigorous no-threshold dominance lock is theorem-shaped only within the declared bounded scope until separately generalized and formalized.",
            "local_only": "Failure of the frozen Q14-selected mechanism on Q13/Q15 controls marks the mechanism local; it does not weaken the direct Q14 J>0 certificate.",
            "dependency_unresolved": "If channel splitting loses sign resolution while direct Method C remains positive, source attribution is interval-condition fragile rather than disproved.",
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
        "completed_leaf_count": result["completed_leaf_count"],
        "mechanism_classification": result["mechanism_classification"],
        "four_way_classification": result["four_way_summary"]["classification"],
        "collapsed_three_way_classification": result["collapsed_three_way_summary"]["classification"],
        "selected_collapsed_uniform_lock_group": result["selected_collapsed_uniform_lock_group"],
        "control_transfer_status": result["control_transfer_status"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
