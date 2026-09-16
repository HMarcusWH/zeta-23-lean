#!/usr/bin/env python3
"""Scope/provenance firewall for the post-#198 parity source-mechanism audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post198_fb05_q14_parity_source_mechanism import joint_mechanism_classification
from probe_post198_fb05_q14_parity_source_mechanism_scope import mechanism_schedule

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post198_fb05_q14_parity_source_mechanism_v1.json"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture["schema_version"] != "POST198_FB05_Q14_PARITY_SOURCE_MECHANISM_FIXTURE_v1":
        raise AssertionError("post-#198 source-mechanism fixture schema drift")
    if fixture["claim_cap"] != "POST198_Q14_PARITY_SOURCE_MECHANISM_RESEARCH_ONLY":
        raise AssertionError("post-#198 source-mechanism claim cap drift")
    if fixture["base_main_sha"] != "87d9bded427571fcd89f13d86f64e1358811a153":
        raise AssertionError("post-#198 base/main provenance drift")
    if fixture["base_main_tree"] != "3a7aa50135ce1b14b4db8c4fec5002041b2db6c3":
        raise AssertionError("post-#198 base tree provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184 or int(fixture["research_authority_pr"]) != 197:
        raise AssertionError("authority split drift")
    if int(fixture["routing_sync_pr"]) != 198:
        raise AssertionError("routing sync drift")
    if int(fixture["arb_precision_bits"]) != 384:
        raise AssertionError("mechanism precision drift")

    locked = (
        (HERE / "fixtures" / fixture["inherited_post197_fixture"], "inherited_post197_fixture_blob_sha"),
        (HERE / fixture["inherited_post197_probe"], "inherited_post197_probe_blob_sha"),
        (HERE / fixture["inherited_post197_replay"], "inherited_post197_replay_blob_sha"),
        (HERE / fixture["canonical_source_backend"], "canonical_source_backend_blob_sha"),
        (HERE / fixture["fixed_unit_value_backend"], "fixed_unit_value_backend_blob_sha"),
        (HERE / fixture["fixed_unit_first_backend"], "fixed_unit_first_backend_blob_sha"),
        (HERE / fixture["four_way_first_backend"], "four_way_first_backend_blob_sha"),
        (HERE / fixture["total_second_backend"], "total_second_backend_blob_sha"),
        (HERE / fixture["sharp_trajectory_backend"], "sharp_trajectory_backend_blob_sha"),
        (HERE / "fixtures" / fixture["source_schedule_fixture"], "source_schedule_fixture_blob_sha"),
    )
    for path, sha_key in locked:
        if not path.exists():
            raise AssertionError(f"locked source missing: {path.name}")
        if git_blob_sha(path) != fixture[sha_key]:
            raise AssertionError(f"locked source drift: {path.name}")

    if tuple(fixture["four_way_channels"]) != ("pole", "arch_signed", "prime_signed", "scalar_shift"):
        raise AssertionError("four-way channel convention drift")
    if tuple(fixture["collapsed_channels"]) != ("pole", "direct_arch_signed", "prime_signed"):
        raise AssertionError("collapsed direct-production channel convention drift")

    policy = fixture["policy"]
    required_true = (
        "post197_completed_cover_replay_required",
        "four_way_second_derivative_independent_check_required",
        "four_way_total_reconstruction_required",
        "normalized_predecessor_coordinates_required",
        "scalar_shift_self_wronskian_zero_required",
        "collapsed_direct_arch_representation_required",
        "direct_method_c_transport_reconstruction_required",
        "control_blind_mechanism_selection_required",
    )
    if not all(bool(policy[key]) for key in required_true):
        raise AssertionError("required mechanism policy disabled")
    forbidden_true = (
        "new_q_n_k_parity_search_permitted",
        "selector_refit_permitted",
        "threshold_refit_permitted",
        "target_sign_import_permitted",
        "precision_increase_permitted",
        "adaptive_budget_increase_permitted",
        "nonlinear_schur_channel_addition_permitted",
        "control_informed_mechanism_selection_permitted",
        "theorem_promotion_permitted",
    )
    if any(bool(policy[key]) for key in forbidden_true):
        raise AssertionError("post-#198 mechanism scope firewall regressed")

    mechanism_text = (HERE / "post198_fb05_q14_parity_source_mechanism.py").read_text(encoding="utf-8")
    backend_text = (HERE / "post198_fb05_q14_four_way_channel_second_derivative.py").read_text(encoding="utf-8")
    required_markers = (
        "normalized_predecessor_channel_jets",
        "scalar_shift_self_wronskian_contains_zero",
        "direct_arch_signed",
        "dominance_margins",
        "four_way_direct_transport_overlap",
        "ADJACENT_Q_TRANSFER",
    )
    if not all(marker in mechanism_text for marker in required_markers):
        raise AssertionError("mechanism implementation lost required structure")
    backend_markers = (
        "four_way_channel_derivative_matrices",
        "c_correction_second_derivative",
        "fixed_unit_four_way_second_derivative_matrices",
        "matrix_second_overlap",
    )
    if not all(marker in backend_text for marker in backend_markers):
        raise AssertionError("four-way second-derivative backend lost required structure")
    forbidden_markers = (
        "post185_fb05_q13_remainder_drift",
        "post189_fb05_joint_selector_separability",
        "normalized_domination_margin",
        "target_margin",
        "max_cells + 1",
        "max_cells+1",
    )
    if any(marker in mechanism_text or marker in backend_text for marker in forbidden_markers):
        raise AssertionError("mechanism implementation contains search/target leakage marker")

    # Pure classifier controls: lock ordering must not invent a stronger class.
    uniform = {"classification": "UNIFORM_LOCK"}
    switching = {"classification": "REGIME_SWITCHING_LOCK"}
    mixed = {"classification": "MIXED_SIGN_NO_SINGLE_LOCK"}
    unresolved = {"classification": "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED"}
    if joint_mechanism_classification(uniform, uniform) != "REPRESENTATION_STABLE_UNIFORM_LOCK":
        raise AssertionError("uniform-lock classifier control failed")
    if joint_mechanism_classification(mixed, uniform) != "DIRECT_ARCH_COLLAPSE_LOCK":
        raise AssertionError("collapsed-lock classifier control failed")
    if joint_mechanism_classification(switching, mixed) != "REGIME_SWITCHING_LOCK":
        raise AssertionError("switching-lock classifier control failed")
    if joint_mechanism_classification(unresolved, uniform) != "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED":
        raise AssertionError("dependency-unresolved classifier control failed")

    schedule = mechanism_schedule(fixture)
    if schedule["primary_box_count"] != 6 or schedule["control_box_count"] != 5:
        raise AssertionError("inherited schedule count drift")
    if int(schedule["primary_hull"]["Q"]) != 14:
        raise AssertionError("mechanism schedule moved off Q14 primary hull")

    print(json.dumps({
        "status": "PASS",
        "base_main_sha": fixture["base_main_sha"],
        "research_authority_pr": fixture["research_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": fixture["arb_precision_bits"],
        "four_way_channels": fixture["four_way_channels"],
        "collapsed_channels": fixture["collapsed_channels"],
        "primary_hull": schedule["primary_hull"],
        "control_blind_mechanism_selection_required": True,
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
