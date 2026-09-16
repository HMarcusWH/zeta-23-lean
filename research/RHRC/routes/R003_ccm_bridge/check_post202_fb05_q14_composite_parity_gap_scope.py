#!/usr/bin/env python3
"""Scope/provenance firewall for the post-#202 full-composite parity-gap audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post202_fb05_q14_composite_parity_gap_mechanism import (
    COOPERATIVE_LOCK,
    DEPENDENCY_UNRESOLVED,
    MIXED_RECONSTRUCTABLE,
    PATTERN_FALSIFIED,
    PATTERN_LOCK,
    summarize_composite_rows,
)
from probe_post202_fb05_q14_composite_parity_gap_scope import composite_schedule

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
FIXTURE = HERE / "fixtures" / "post202_fb05_q14_composite_parity_gap_v1.json"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def _synthetic_row(*, gap_positive: bool, pattern: bool, cooperative: bool) -> dict:
    return {
        "pattern_lock": pattern,
        "cooperative_lock": cooperative,
        "factor_checks": {"gap_transport_strict_positive": gap_positive},
    }


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture["schema_version"] != "POST202_FB05_Q14_COMPOSITE_PARITY_GAP_FIXTURE_v1":
        raise AssertionError("post-#202 composite fixture schema drift")
    if fixture["claim_cap"] != "POST202_Q14_COMPOSITE_PARITY_GAP_RESEARCH_ONLY":
        raise AssertionError("post-#202 composite claim cap drift")
    if fixture["base_main_sha"] != "cd556456c661c797c3602f90c1f54e24add08acd":
        raise AssertionError("post-#202 base/main provenance drift")
    if fixture["base_main_tree"] != "7077b57882d7a1970ceae52cb6d100fd7ace28d2":
        raise AssertionError("post-#202 base tree provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184:
        raise AssertionError("theorem authority drift")
    if int(fixture["research_authority_pr"]) != 201:
        raise AssertionError("research authority drift")
    if int(fixture["routing_sync_pr"]) != 202:
        raise AssertionError("routing sync drift")
    if int(fixture["arb_precision_bits"]) != 384:
        raise AssertionError("composite audit precision drift")

    locked = (
        (HERE / "fixtures" / fixture["inherited_post201_fixture"], "inherited_post201_fixture_blob_sha"),
        (HERE / fixture["inherited_post201_backend"], "inherited_post201_backend_blob_sha"),
        (HERE / fixture["inherited_post201_paired_backend"], "inherited_post201_paired_backend_blob_sha"),
        (HERE / fixture["inherited_post201_scope_check"], "inherited_post201_scope_check_blob_sha"),
        (HERE / fixture["inherited_post201_probe"], "inherited_post201_probe_blob_sha"),
        (HERE / fixture["inherited_post201_certifier"], "inherited_post201_certifier_blob_sha"),
        (ROOT / fixture["theorem_scalar_split_source"], "theorem_scalar_split_source_blob_sha"),
        (ROOT / fixture["theorem_parity_log_source"], "theorem_parity_log_source_blob_sha"),
        (HERE / fixture["trajectory_transport_backend"], "trajectory_transport_backend_blob_sha"),
    )
    for path, sha_key in locked:
        if not path.exists():
            raise AssertionError(f"locked source missing: {path}")
        if git_blob_sha(path) != fixture[sha_key]:
            raise AssertionError(f"locked source drift: {path.name}")

    expected_pattern = {
        "E": "STRICT_POSITIVE",
        "G": "STRICT_POSITIVE",
        "G_prime": "NONNEGATIVE",
        "E_prime": "NONPOSITIVE",
    }
    if fixture["center_kill_switch_pattern"] != expected_pattern:
        raise AssertionError("predeclared center kill-switch pattern drift")

    expected_classes = {
        PATTERN_FALSIFIED,
        PATTERN_LOCK,
        COOPERATIVE_LOCK,
        MIXED_RECONSTRUCTABLE,
        DEPENDENCY_UNRESOLVED,
    }
    if set(fixture["permitted_mechanism_classifications"]) != expected_classes:
        raise AssertionError("composite classification surface drift")

    policy = fixture["policy"]
    required_true = (
        "post197_completed_cover_replay_required",
        "post201_disposition_replay_required",
        "theorem_aligned_scalar_split_required",
        "scalar_cancellation_before_interval_transport_required",
        "full_composite_only_classifier_required",
        "exact_center_kill_switch_required",
        "center_gate_before_full_cover_required",
        "direct_method_c_transport_reconstruction_required",
        "exact_inherited_leaf_partition_required",
        "control_blind_mechanism_selection_required",
    )
    if not all(bool(policy[key]) for key in required_true):
        raise AssertionError("required composite policy disabled")
    forbidden_true = (
        "new_q_n_k_parity_search_permitted",
        "source_channel_selector_permitted",
        "selector_refit_permitted",
        "threshold_refit_permitted",
        "target_sign_import_permitted",
        "precision_increase_permitted",
        "adaptive_budget_increase_permitted",
        "center_pattern_rescue_search_permitted",
        "control_informed_mechanism_selection_permitted",
        "theorem_promotion_permitted",
    )
    if any(bool(policy[key]) for key in forbidden_true):
        raise AssertionError("post-#202 composite scope firewall regressed")

    backend_text = (HERE / "post202_fb05_q14_parity_contrast_jets.py").read_text(encoding="utf-8")
    mechanism_text = (HERE / "post202_fb05_q14_composite_parity_gap_mechanism.py").read_text(encoding="utf-8")
    checker_text = (HERE / "check_post202_fb05_q14_parity_contrast_jets_scope.py").read_text(encoding="utf-8")
    required_backend_markers = (
        "fixed_unit_gamma_core",
        "exact_parity_gap_contrast_matrix",
        "contrast.trace()",
        "scalar_free_full_composite_matrix_jets",
        "_arb_matrix_from_sympy_rational",
        "fmpq",
        '"exact_rational_contrast_conversion": True',
        '"scalar_removed_before_contraction": True',
        "pole_component_prime",
        "prime_component_second",
    )
    if not all(marker in backend_text for marker in required_backend_markers):
        raise AssertionError("composite backend lost theorem-aligned scalar-cancellation/rational structure")
    required_checker_markers = (
        "_independent_normalized_gap",
        "G_matches_independent_O_minus_E",
        "G_prime_matches_independent_O_prime_minus_E_prime",
        "G_second_matches_independent_O_second_minus_E_second",
    )
    if not all(marker in checker_text for marker in required_checker_markers):
        raise AssertionError("contrast checker lost independent normalized O-E reconstruction")
    required_mechanism_markers = (
        "exact_center_kill_switch(schedule)",
        'if not gate["survives"]',
        "centered_first_derivative_enclosure",
        "J_center = E0 * Gp0 - Ep0 * G0",
        "J_prime_interval = E * GppI - EppI * G",
        "T1 = E * Gp",
        "T2 = -Ep * G",
        "gap_transport_direct_method_c_overlap",
    )
    if not all(marker in mechanism_text for marker in required_mechanism_markers):
        raise AssertionError("composite mechanism lost required full-object structure")
    forbidden_markers = (
        "dominance_locks",
        "source_sum_positive",
        "normalized_domination_margin",
        "target_margin",
        "max_cells + 1",
        "max_cells+1",
        "post189_fb05_joint_selector_separability",
        "_arb_matrix_from_sympy(",
    )
    if any(marker in backend_text or marker in mechanism_text for marker in forbidden_markers):
        raise AssertionError("composite mechanism contains source-selector/search/integer-conversion leakage marker")

    # Frozen classifier controls, independent of numerical output.
    if summarize_composite_rows([
        _synthetic_row(gap_positive=True, pattern=True, cooperative=True)
    ])["classification"] != PATTERN_LOCK:
        raise AssertionError("pattern-lock classifier control failed")
    if summarize_composite_rows([
        _synthetic_row(gap_positive=True, pattern=False, cooperative=True)
    ])["classification"] != COOPERATIVE_LOCK:
        raise AssertionError("cooperative classifier control failed")
    if summarize_composite_rows([
        _synthetic_row(gap_positive=True, pattern=False, cooperative=False)
    ])["classification"] != MIXED_RECONSTRUCTABLE:
        raise AssertionError("mixed classifier control failed")
    if summarize_composite_rows([
        _synthetic_row(gap_positive=False, pattern=True, cooperative=True)
    ])["classification"] != DEPENDENCY_UNRESOLVED:
        raise AssertionError("dependency-unresolved classifier control failed")

    schedule = composite_schedule(fixture)
    if schedule["primary_box_count"] != 6 or schedule["control_box_count"] != 5:
        raise AssertionError("inherited schedule count drift")
    if int(schedule["primary_hull"]["Q"]) != 14:
        raise AssertionError("composite schedule moved off Q14 primary hull")

    print(json.dumps({
        "status": "PASS",
        "base_main_sha": fixture["base_main_sha"],
        "research_authority_pr": fixture["research_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": fixture["arb_precision_bits"],
        "center_kill_switch_pattern": fixture["center_kill_switch_pattern"],
        "primary_hull": schedule["primary_hull"],
        "full_composite_only_classifier_required": True,
        "exact_rational_contrast_conversion_required": True,
        "independent_normalized_O_minus_E_reconstruction_required": True,
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
