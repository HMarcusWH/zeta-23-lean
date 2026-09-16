#!/usr/bin/env python3
"""Scope/provenance firewall for the post-#200 discrepancy-mechanism audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post200_fb05_q14_discrepancy_mechanism import (
    ARCH_GROUP,
    CROSS_GROUP,
    DISCREPANCY_GROUP,
    summarize_paired_representation,
)
from probe_post200_fb05_q14_discrepancy_mechanism_scope import discrepancy_schedule

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post200_fb05_q14_discrepancy_mechanism_v1.json"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def _synthetic_row(*, positive: bool, locks: tuple[str, ...] = (), nonnegative: bool = False) -> dict:
    return {
        "paired": {
            "dominance_locks": list(locks),
            "source_sum_positive": positive,
            "all_groups_nonnegative": nonnegative,
        }
    }


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture["schema_version"] != "POST200_FB05_Q14_DISCREPANCY_MECHANISM_FIXTURE_v1":
        raise AssertionError("post-#200 discrepancy fixture schema drift")
    if fixture["claim_cap"] != "POST200_Q14_DISCREPANCY_MECHANISM_RESEARCH_ONLY":
        raise AssertionError("post-#200 discrepancy claim cap drift")
    if fixture["base_main_sha"] != "759c2146a74b8374ec80a97fa2ae4e4e51ab54c0":
        raise AssertionError("post-#200 base/main provenance drift")
    if fixture["base_main_tree"] != "d4be5ed50d02e162c6226aeb8a0729698f995844":
        raise AssertionError("post-#200 base tree provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184:
        raise AssertionError("theorem authority drift")
    if int(fixture["research_authority_pr"]) != 199:
        raise AssertionError("research authority drift")
    if int(fixture["routing_sync_pr"]) != 200:
        raise AssertionError("routing sync drift")
    if int(fixture["arb_precision_bits"]) != 384:
        raise AssertionError("discrepancy mechanism precision drift")

    locked = (
        (HERE / "fixtures" / fixture["inherited_post199_fixture"], "inherited_post199_fixture_blob_sha"),
        (HERE / fixture["inherited_four_way_backend"], "inherited_four_way_backend_blob_sha"),
        (HERE / fixture["inherited_source_mechanism_backend"], "inherited_source_mechanism_backend_blob_sha"),
        (HERE / fixture["inherited_source_mechanism_scope_check"], "inherited_source_mechanism_scope_check_blob_sha"),
        (HERE / fixture["inherited_source_mechanism_probe"], "inherited_source_mechanism_probe_blob_sha"),
        (HERE / fixture["inherited_source_mechanism_certifier"], "inherited_source_mechanism_certifier_blob_sha"),
        (HERE / fixture["inherited_four_way_second_check"], "inherited_four_way_second_check_blob_sha"),
    )
    for path, sha_key in locked:
        if not path.exists():
            raise AssertionError(f"locked source missing: {path.name}")
        if git_blob_sha(path) != fixture[sha_key]:
            raise AssertionError(f"locked source drift: {path.name}")

    if tuple(fixture["paired_channels"]) != ("pole_prime_discrepancy", "direct_arch_signed"):
        raise AssertionError("paired channel convention drift")

    expected_classes = {
        "DISCREPANCY_UNIFORM_LOCK",
        "DIRECT_ARCH_UNIFORM_LOCK",
        "CROSS_UNIFORM_LOCK",
        "REGIME_SWITCHING_LOCK",
        "COOPERATIVE_NONNEGATIVE",
        "MIXED_SIGN_RECONSTRUCTABLE",
        "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
    }
    if set(fixture["permitted_mechanism_classifications"]) != expected_classes:
        raise AssertionError("paired mechanism classification surface drift")

    policy = fixture["policy"]
    required_true = (
        "post197_completed_cover_replay_required",
        "post199_scope_firewall_required",
        "paired_matrix_jet_reconstruction_required",
        "pairing_before_parity_restriction_required",
        "normalized_predecessor_coordinates_required",
        "direct_method_c_transport_reconstruction_required",
        "exact_inherited_leaf_partition_required",
        "control_blind_mechanism_selection_required",
    )
    if not all(bool(policy[key]) for key in required_true):
        raise AssertionError("required discrepancy policy disabled")
    forbidden_true = (
        "new_q_n_k_parity_search_permitted",
        "selector_refit_permitted",
        "threshold_refit_permitted",
        "target_sign_import_permitted",
        "precision_increase_permitted",
        "adaptive_budget_increase_permitted",
        "post_transport_pole_prime_regrouping_permitted",
        "control_informed_mechanism_selection_permitted",
        "theorem_promotion_permitted",
    )
    if any(bool(policy[key]) for key in forbidden_true):
        raise AssertionError("post-#200 discrepancy scope firewall regressed")

    backend_text = (HERE / "post200_fb05_q14_discrepancy_channel_jets.py").read_text(encoding="utf-8")
    mechanism_text = (HERE / "post200_fb05_q14_discrepancy_mechanism.py").read_text(encoding="utf-8")
    required_backend_markers = (
        'channels["pole"]',
        'channels["prime_signed"]',
        "paired_discrepancy_channel_jets",
        "matrix_prime",
        "matrix_second",
        "paired_reconstruction",
    )
    if not all(marker in backend_text for marker in required_backend_markers):
        raise AssertionError("paired backend lost upstream pairing markers")
    required_mechanism_markers = (
        "normalized_predecessor_channel_jets(center_jets)",
        "interaction_transport(center, interval",
        "paired_direct_transport_overlap",
        "pole_prime_discrepancy__x__direct_arch_signed",
        "MIXED_SIGN_RECONSTRUCTABLE",
        "ADJACENT_Q_TRANSFER",
    )
    if not all(marker in mechanism_text for marker in required_mechanism_markers):
        raise AssertionError("paired mechanism implementation lost required structure")
    forbidden_markers = (
        "max_cells + 1",
        "max_cells+1",
        "normalized_domination_margin",
        "target_margin",
        "post189_fb05_joint_selector_separability",
    )
    if any(marker in backend_text or marker in mechanism_text for marker in forbidden_markers):
        raise AssertionError("paired mechanism contains search/target leakage marker")

    # Classifier controls: exact outcomes are frozen before numerical execution.
    if summarize_paired_representation([
        _synthetic_row(positive=True, locks=(DISCREPANCY_GROUP,))
    ])["classification"] != "DISCREPANCY_UNIFORM_LOCK":
        raise AssertionError("discrepancy uniform-lock classifier control failed")
    if summarize_paired_representation([
        _synthetic_row(positive=True, locks=(ARCH_GROUP,))
    ])["classification"] != "DIRECT_ARCH_UNIFORM_LOCK":
        raise AssertionError("arch uniform-lock classifier control failed")
    if summarize_paired_representation([
        _synthetic_row(positive=True, locks=(CROSS_GROUP,))
    ])["classification"] != "CROSS_UNIFORM_LOCK":
        raise AssertionError("cross uniform-lock classifier control failed")
    if summarize_paired_representation([
        _synthetic_row(positive=True, locks=(DISCREPANCY_GROUP,)),
        _synthetic_row(positive=True, locks=(ARCH_GROUP,)),
    ])["classification"] != "REGIME_SWITCHING_LOCK":
        raise AssertionError("regime-switching classifier control failed")
    if summarize_paired_representation([
        _synthetic_row(positive=True, nonnegative=True)
    ])["classification"] != "COOPERATIVE_NONNEGATIVE":
        raise AssertionError("cooperative classifier control failed")
    if summarize_paired_representation([
        _synthetic_row(positive=True, nonnegative=False)
    ])["classification"] != "MIXED_SIGN_RECONSTRUCTABLE":
        raise AssertionError("mixed reconstructable classifier control failed")
    if summarize_paired_representation([
        _synthetic_row(positive=False)
    ])["classification"] != "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED":
        raise AssertionError("dependency-unresolved classifier control failed")

    schedule = discrepancy_schedule(fixture)
    if schedule["primary_box_count"] != 6 or schedule["control_box_count"] != 5:
        raise AssertionError("inherited schedule count drift")
    if int(schedule["primary_hull"]["Q"]) != 14:
        raise AssertionError("discrepancy schedule moved off Q14 primary hull")

    print(json.dumps({
        "status": "PASS",
        "base_main_sha": fixture["base_main_sha"],
        "research_authority_pr": fixture["research_authority_pr"],
        "routing_sync_pr": fixture["routing_sync_pr"],
        "precision_bits": fixture["arb_precision_bits"],
        "paired_channels": fixture["paired_channels"],
        "primary_hull": schedule["primary_hull"],
        "control_blind_mechanism_selection_required": True,
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
