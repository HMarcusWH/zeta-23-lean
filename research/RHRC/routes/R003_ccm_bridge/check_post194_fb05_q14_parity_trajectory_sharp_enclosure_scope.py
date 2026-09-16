#!/usr/bin/env python3
"""Plumbing/provenance guards for the post-#194 sharp trajectory audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post194_fb05_q14_parity_trajectory_sharp_enclosure import (
    synthetic_second_order_controls,
)
from probe_post194_fb05_q14_parity_trajectory_sharp_enclosure_scope import (
    sharp_trajectory_schedule,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post194_fb05_q14_parity_trajectory_sharp_enclosure_v1.json"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture["schema_version"] != "POST194_FB05_Q14_PARITY_TRAJECTORY_SHARP_ENCLOSURE_FIXTURE_v1":
        raise AssertionError("post-#194 sharp fixture schema drift")
    if fixture["claim_cap"] != "POST194_Q14_PARITY_TRAJECTORY_SHARP_RESEARCH_ONLY":
        raise AssertionError("post-#194 sharp claim cap drift")
    if fixture["base_main_sha"] != "05dedbec3c65cba08057058616737a707215a00a":
        raise AssertionError("post-#194 base/main provenance drift")
    if fixture["base_main_tree"] != "48bcbb38953fc13883773a1eea5dc2aeb2c26985":
        raise AssertionError("post-#194 base tree provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184:
        raise AssertionError("theorem authority drift")
    if int(fixture["research_authority_pr"]) != 193:
        raise AssertionError("research authority drift")
    if int(fixture["routing_sync_pr"]) != 194:
        raise AssertionError("routing sync drift")
    if int(fixture["arb_precision_bits"]) != 384:
        raise AssertionError("trajectory precision drift")
    if int(fixture["max_refinement_depth"]) != 12 or int(fixture["max_evaluated_cells"]) != 96:
        raise AssertionError("trajectory refinement budget drift")

    locked_sources = (
        (HERE / fixture["post193_module"], "post193_module_blob_sha"),
        (HERE / "fixtures" / fixture["post193_fixture"], "post193_fixture_blob_sha"),
        (HERE / fixture["post193_probe"], "post193_probe_blob_sha"),
        (HERE / fixture["fixed_unit_derivative_module"], "fixed_unit_derivative_module_blob_sha"),
        (HERE / "fixtures" / fixture["inherited_schedule_fixture"], "inherited_schedule_fixture_blob_sha"),
        (HERE / fixture["inherited_schedule_probe"], "inherited_schedule_probe_blob_sha"),
        (HERE / fixture["second_derivative_backend"], "second_derivative_backend_blob_sha"),
        (HERE / fixture["sharp_trajectory_module"], "sharp_trajectory_module_blob_sha"),
    )
    for path, sha_key in locked_sources:
        if not path.exists():
            raise AssertionError(f"locked source missing: {path.name}")
        if git_blob_sha(path) != fixture[sha_key]:
            raise AssertionError(f"locked source content drift: {path.name}")

    policy = fixture["policy"]
    forbidden_true = (
        "new_q_n_parity_search_permitted",
        "selector_refit_permitted",
        "threshold_refit_permitted",
        "new_selector_features_permitted",
        "target_sign_import_permitted",
        "larger_precision_permitted",
        "larger_refinement_budget_permitted",
        "bounded_nonresolution_counts_as_exclusion",
    )
    if any(bool(policy[key]) for key in forbidden_true):
        raise AssertionError("post-#194 search/claim firewall regressed")
    required_true = (
        "shared_cell_abc_comparison_required",
        "post193_baseline_replay_required",
        "second_derivative_independent_check_required",
    )
    if not all(bool(policy[key]) for key in required_true):
        raise AssertionError("post-#194 required comparison/validation policy disabled")

    sharp_text = (HERE / fixture["sharp_trajectory_module"]).read_text(encoding="utf-8")
    backend_text = (HERE / fixture["second_derivative_backend"]).read_text(encoding="utf-8")
    forbidden_markers = (
        "post185_fb05_q13_remainder_drift",
        "post189_fb05_joint_selector_separability",
        "normalized_domination_margin",
        "target_margin",
    )
    for marker in forbidden_markers:
        if marker in sharp_text or marker in backend_text:
            raise AssertionError(f"target leakage marker present: {marker}")

    schedule = sharp_trajectory_schedule(fixture)
    if schedule["primary_box_count"] != 6 or schedule["control_box_count"] != 5:
        raise AssertionError("sharp trajectory inherited schedule count drift")
    hull = schedule["primary_hull"]
    if hull["Q"] != 14 or not 0 <= hull["lo_num"] < hull["hi_num"] <= hull["den"]:
        raise AssertionError("invalid frozen Q14 primary hull")

    controls = synthetic_second_order_controls()
    if controls["status"] != "PASS":
        raise AssertionError("sharp trajectory synthetic controls failed")

    print(
        json.dumps(
            {
                "status": "PASS",
                "base_main_sha": fixture["base_main_sha"],
                "primary_box_count": schedule["primary_box_count"],
                "control_box_count": schedule["control_box_count"],
                "primary_hull": hull,
                "precision_bits": fixture["arb_precision_bits"],
                "max_refinement_depth": fixture["max_refinement_depth"],
                "max_evaluated_cells": fixture["max_evaluated_cells"],
                "synthetic_controls": controls["status"],
                "new_selector_features_permitted": False,
                "target_sign_import_permitted": False,
                "theorem_promotion": False,
                "rh_claim": False,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
