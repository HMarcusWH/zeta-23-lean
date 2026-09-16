#!/usr/bin/env python3
"""Certify the frozen post-#190 canonical-realizability audit."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from post190_fb05_canonical_realizability import (
    LAYER_IDS,
    audit_all_layers,
)
from probe_post190_fb05_canonical_realizability_scope import canonical_realizability_schedule

HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "post190_fb05_canonical_realizability_v1.json"
POST190_FIXTURE = HERE / "fixtures" / "post189_fb05_joint_selector_separability_v1.json"
SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"


def _validate_schedule(fixture: dict, schedule: dict) -> None:
    expected = canonical_realizability_schedule(fixture)
    keys = (
        "schema_version",
        "status",
        "claim_cap",
        "base_main_sha",
        "theorem_authority_pr",
        "research_authority_pr",
        "routing_sync_pr",
        "selected_target",
        "required_ancestry_control",
        "arb_precision_bits",
        "layer_ids",
        "boxes",
        "primary_box_count",
        "control_box_count",
        "policy",
    )
    for key in keys:
        if schedule.get(key) != expected.get(key):
            raise AssertionError(f"canonical-realizability schedule drift: {key}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_FIXTURE)
    ap.add_argument("--schedule", type=Path, required=True)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path("/tmp/POST190_FB05_CANONICAL_REALIZABILITY_CERTIFICATE.json"),
    )
    args = ap.parse_args()

    fixture = json.loads(args.input.read_text(encoding="utf-8"))
    post190_fixture = json.loads(POST190_FIXTURE.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SELECTOR_FIXTURE.read_text(encoding="utf-8"))
    schedule = json.loads(args.schedule.read_text(encoding="utf-8"))
    _validate_schedule(fixture, schedule)

    result = audit_all_layers(
        selector_fixture,
        post190_fixture,
        schedule,
        precision_bits=int(fixture["arb_precision_bits"]),
    )
    if result["status"] != "PASS":
        raise AssertionError("canonical-realizability audit did not execute cleanly")
    layers = {row["layer"]: row for row in result["layers"]}
    if tuple(layers) != LAYER_IDS:
        raise AssertionError("canonical-realizability result layer order drift")

    required = fixture["required_specific_witness_dispositions"]
    for layer_id, classification in required.items():
        if layers[layer_id]["classification"] != classification:
            raise AssertionError(f"unexpected disposition at {layer_id}")
    if layers[LAYER_IDS[2]]["general_reflection_control"]["classification"] != fixture["required_general_scalar_control_disposition"]:
        raise AssertionError("general scalar-law reflection control failed")
    for layer_id in LAYER_IDS[3:]:
        if layers[layer_id]["classification"] != fixture["bounded_layers_required_disposition"]:
            raise AssertionError(f"bounded layer overclaim at {layer_id}")

    if not layers[LAYER_IDS[3]]["all_matrix_level_arch_scalar_couplings_overlap"]:
        raise AssertionError("same-aperture arch/scalar production coupling failed")
    if layers[LAYER_IDS[3]]["primary_state_count"] != int(fixture["expected_primary_box_count"]):
        raise AssertionError("Layer 3 primary state count drift")
    if layers[LAYER_IDS[4]]["primary_state_count"] != int(fixture["expected_primary_box_count"]):
        raise AssertionError("Layer 4 primary state count drift")
    if not layers[LAYER_IDS[5]]["all_in_scope_channel_reconstructions_overlap"]:
        raise AssertionError("full canonical channel reconstruction failed")
    if layers[LAYER_IDS[5]]["state_count"] != int(fixture["expected_primary_box_count"]) + int(fixture["expected_control_box_count"]):
        raise AssertionError("Layer 5 state count drift")

    if result["general_reflection_excluded"]:
        raise AssertionError("bounded audit overclaimed general reflection exclusion")
    if result["theorem_promotion"] or result["fb05_closed"] or result["negative_root_exclusion"] or result["rh_claim"]:
        raise AssertionError("canonical-realizability claim firewall regression")

    out = {
        "schema_version": "POST190_FB05_CANONICAL_REALIZABILITY_CERTIFICATE_v1",
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
        "result": result,
        "interpretation": {
            "specific_post190_witness": "The exact #190 ambient twin survives source-channel bookkeeping but is excluded once the actual positive scalar-aperture law is imposed.",
            "general_reflection": "An exact symbolic adversarial construction using two actual positive scalar-law values shows that the scalar law alone does not eliminate the general reflection mechanism.",
            "bounded_canonical_replay": "The inherited Q14/N2->K3/even canonical schedule is replayed through common-aperture channels, actual Schur geometry, and full production reconstruction. Any failure to exhibit an exact twin remains UNRESOLVED.",
            "next_question": "Which additional same-aperture production relation, trajectory-rigidity law, or independent same-state invariant can exclude the general reflected twin class?"
        },
        "nonclaims": fixture["nonclaims"],
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")

    scalar_samples = layers[LAYER_IDS[2]]["general_reflection_control"]["actual_scalar_samples"]
    print(json.dumps({
        "status": "PASS",
        "layer0": layers[LAYER_IDS[0]]["classification"],
        "layer1": layers[LAYER_IDS[1]]["classification"],
        "layer2_specific": layers[LAYER_IDS[2]]["classification"],
        "layer2_general_reflection": layers[LAYER_IDS[2]]["general_reflection_control"]["classification"],
        "layer2_scalar_higher_ball": scalar_samples["higher"]["chi_scalar"]["ball"],
        "layer2_scalar_lower_ball": scalar_samples["lower"]["chi_scalar"]["ball"],
        "layer3": layers[LAYER_IDS[3]]["classification"],
        "layer3_all_arch_scalar_couplings_overlap": layers[LAYER_IDS[3]]["all_matrix_level_arch_scalar_couplings_overlap"],
        "layer4": layers[LAYER_IDS[4]]["classification"],
        "layer4_pair_count": layers[LAYER_IDS[4]]["pair_count"],
        "layer4_strong_vector_overlap_pair_count": layers[LAYER_IDS[4]]["strong_vector_overlap_pair_count"],
        "layer4_overlap_and_opposite_target_pair_count": layers[LAYER_IDS[4]]["strong_vector_overlap_and_opposite_target_pair_count"],
        "layer5": layers[LAYER_IDS[5]]["classification"],
        "layer5_certified_h1_state_count": layers[LAYER_IDS[5]]["certified_h1_state_count"],
        "layer5_all_channel_reconstructions_overlap": layers[LAYER_IDS[5]]["all_in_scope_channel_reconstructions_overlap"],
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
