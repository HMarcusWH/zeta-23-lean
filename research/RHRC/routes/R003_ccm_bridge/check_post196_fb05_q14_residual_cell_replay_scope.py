#!/usr/bin/env python3
"""Provenance and scope firewall for the post-#196 residual-cell replay."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from probe_post196_fb05_q14_residual_cell_replay_scope import residual_replay_schedule

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post196_fb05_q14_residual_cell_replay_v1.json"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture["schema_version"] != "POST196_FB05_Q14_RESIDUAL_CELL_REPLAY_FIXTURE_v1":
        raise AssertionError("post-#196 residual fixture schema drift")
    if fixture["claim_cap"] != "POST196_Q14_UNIQUE_BUDGET_LEAF_REPLAY_RESEARCH_ONLY":
        raise AssertionError("post-#196 residual claim cap drift")
    if fixture["base_main_sha"] != "6d43209a7a392927169d1d1765704e8510fefbfc":
        raise AssertionError("post-#196 base/main provenance drift")
    if fixture["base_main_tree"] != "9afe818a74edfe74055758a7aa5874163255d774":
        raise AssertionError("post-#196 base tree provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184:
        raise AssertionError("theorem authority drift")
    if int(fixture["research_authority_pr"]) != 195:
        raise AssertionError("research authority drift")
    if int(fixture["routing_sync_pr"]) != 196:
        raise AssertionError("routing sync drift")
    if int(fixture["arb_precision_bits"]) != 384:
        raise AssertionError("residual replay precision drift")
    if int(fixture["max_refinement_depth"]) != 12 or int(fixture["max_evaluated_cells"]) != 96:
        raise AssertionError("inherited post-#195 refinement budget drift")
    if int(fixture["followup_evaluated_cells"]) != 1:
        raise AssertionError("residual replay must evaluate exactly one follow-up cell")

    locked_sources = (
        (HERE / fixture["inherited_post195_module"], "inherited_post195_module_blob_sha"),
        (HERE / "fixtures" / fixture["inherited_post195_fixture"], "inherited_post195_fixture_blob_sha"),
        (HERE / fixture["inherited_post195_probe"], "inherited_post195_probe_blob_sha"),
        (HERE / fixture["inherited_post195_certifier"], "inherited_post195_certifier_blob_sha"),
    )
    for path, sha_key in locked_sources:
        if not path.exists():
            raise AssertionError(f"locked post-#195 source missing: {path.name}")
        if git_blob_sha(path) != fixture[sha_key]:
            raise AssertionError(f"locked post-#195 source drift: {path.name}")

    policy = fixture["policy"]
    required_true = (
        "repeat_post195_audit_required",
        "unique_budget_leaf_required",
        "one_cell_followup_only",
        "inherited_evaluator_required",
        "completed_cover_reclassification_required",
    )
    if not all(bool(policy[key]) for key in required_true):
        raise AssertionError("required residual replay policy disabled")
    forbidden_true = (
        "new_q_n_parity_search_permitted",
        "selector_refit_permitted",
        "threshold_refit_permitted",
        "target_sign_import_permitted",
        "precision_increase_permitted",
        "adaptive_budget_increase_permitted",
        "recursive_followup_subdivision_permitted",
        "source_mechanism_refit_permitted",
        "bounded_nonresolution_counts_as_exclusion",
    )
    if any(bool(policy[key]) for key in forbidden_true):
        raise AssertionError("post-#196 residual replay scope firewall regressed")

    replay_text = (HERE / "post196_fb05_q14_residual_cell_replay.py").read_text(encoding="utf-8")
    required_markers = (
        "audit_sharp_parity_trajectory",
        "sharp_trajectory_cell_record",
        '"MAX_CELL_BUDGET"',
        "followup_evaluated_cell_count",
        "recursive_followup_subdivision",
    )
    if not all(marker in replay_text for marker in required_markers):
        raise AssertionError("residual replay no longer uses the inherited one-cell path")
    forbidden_markers = (
        "max_cells + 1",
        "max_cells+1",
        "normalized_domination_margin",
        "target_margin",
        "post189_fb05_joint_selector_separability",
    )
    if any(marker in replay_text for marker in forbidden_markers):
        raise AssertionError("residual replay contains budget/search leakage marker")

    schedule = residual_replay_schedule(fixture)
    if schedule["primary_box_count"] != 6 or schedule["control_box_count"] != 5:
        raise AssertionError("inherited post-#195 schedule count drift")
    hull = schedule["primary_hull"]
    if hull["Q"] != 14 or not 0 <= hull["lo_num"] < hull["hi_num"] <= hull["den"]:
        raise AssertionError("invalid inherited Q14 primary hull")

    print(json.dumps({
        "status": "PASS",
        "base_main_sha": fixture["base_main_sha"],
        "research_authority_pr": fixture["research_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": fixture["arb_precision_bits"],
        "max_evaluated_cells": fixture["max_evaluated_cells"],
        "followup_evaluated_cells": fixture["followup_evaluated_cells"],
        "primary_hull": hull,
        "adaptive_budget_increase_permitted": False,
        "recursive_followup_subdivision_permitted": False,
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
