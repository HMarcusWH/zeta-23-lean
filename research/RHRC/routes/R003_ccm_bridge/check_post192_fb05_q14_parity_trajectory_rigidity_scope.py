#!/usr/bin/env python3
"""Plumbing/provenance guards for the post-#192 parity-trajectory audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post192_fb05_q14_parity_trajectory_rigidity import synthetic_orientation_controls
from probe_post192_fb05_q14_parity_trajectory_rigidity_scope import parity_trajectory_schedule

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post192_fb05_q14_parity_trajectory_rigidity_v1.json"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture["schema_version"] != "POST192_FB05_Q14_PARITY_TRAJECTORY_RIGIDITY_FIXTURE_v1":
        raise AssertionError("post-#192 parity trajectory fixture schema drift")
    if fixture["claim_cap"] != "POST192_Q14_PARITY_TRAJECTORY_RESEARCH_ONLY":
        raise AssertionError("post-#192 parity trajectory claim cap drift")
    if fixture["base_main_sha"] != "c3e4c8012945d6b86c2236d9e0cce27e3a4c20d9":
        raise AssertionError("post-#192 base/main provenance drift")
    if fixture["base_main_tree"] != "8dbbf620ebd3668350ad9978c6313d75e754885c":
        raise AssertionError("post-#192 base tree provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184:
        raise AssertionError("theorem authority drift")
    if int(fixture["research_authority_pr"]) != 192:
        raise AssertionError("research authority drift")
    if int(fixture["routing_sync_pr"]) != 191:
        raise AssertionError("routing synchronization provenance drift")
    if int(fixture["arb_precision_bits"]) != 384:
        raise AssertionError("trajectory precision drift")
    if int(fixture["selected_target"]["primary_Q"]) != 14:
        raise AssertionError("trajectory primary Q drift")

    locked_sources = (
        (HERE / fixture["post192_module"], "post192_module_blob_sha"),
        (HERE / "fixtures" / fixture["post192_fixture"], "post192_fixture_blob_sha"),
        (HERE / fixture["source_selector_module"], "source_selector_module_blob_sha"),
        (HERE / fixture["fixed_unit_derivative_module"], "fixed_unit_derivative_module_blob_sha"),
        (HERE / "fixtures" / fixture["inherited_schedule_fixture"], "inherited_schedule_fixture_blob_sha"),
        (HERE / fixture["inherited_schedule_probe"], "inherited_schedule_probe_blob_sha"),
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
        "arb_overlap_counts_as_exact_equality",
        "bounded_nonresolution_counts_as_exclusion",
    )
    if any(bool(policy[key]) for key in forbidden_true):
        raise AssertionError("post-#192 trajectory claim/search firewall regressed")
    if not bool(policy["deterministic_dyadic_refinement_inside_frozen_hull_permitted"]):
        raise AssertionError("deterministic trajectory localizer unexpectedly disabled")
    if not bool(policy["centered_mean_value_h1_required"]):
        raise AssertionError("centered H1 recovery requirement unexpectedly disabled")

    source_text = (HERE / "post192_fb05_q14_parity_trajectory_rigidity.py").read_text(encoding="utf-8")
    forbidden_import_markers = (
        "from post185_fb05_q13_remainder_drift",
        "import post185_fb05_q13_remainder_drift",
        "from post189_fb05_joint_selector_separability",
        "import post189_fb05_joint_selector_separability",
        "target_margin",
    )
    for marker in forbidden_import_markers:
        if marker in source_text:
            raise AssertionError(f"target leakage marker present in trajectory backend: {marker}")

    schedule = parity_trajectory_schedule(fixture)
    if schedule["primary_box_count"] != int(fixture["expected_primary_box_count"]):
        raise AssertionError("trajectory primary schedule count drift")
    if schedule["control_box_count"] != int(fixture["expected_control_box_count"]):
        raise AssertionError("trajectory control schedule count drift")
    hull = schedule["primary_hull"]
    if hull["Q"] != 14 or not 0 <= hull["lo_num"] < hull["hi_num"] <= hull["den"]:
        raise AssertionError("invalid frozen primary trajectory hull")

    controls = synthetic_orientation_controls()
    if controls["status"] != "PASS":
        raise AssertionError("exact synthetic Wronskian orientation controls failed")

    print(json.dumps({
        "status": "PASS",
        "base_main_sha": fixture["base_main_sha"],
        "primary_box_count": schedule["primary_box_count"],
        "control_box_count": schedule["control_box_count"],
        "primary_hull": hull,
        "max_refinement_depth": schedule["max_refinement_depth"],
        "max_evaluated_cells": schedule["max_evaluated_cells"],
        "synthetic_controls": controls["status"],
        "new_selector_features_permitted": False,
        "target_sign_import_permitted": False,
        "theorem_promotion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
