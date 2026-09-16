#!/usr/bin/env python3
"""Plumbing/provenance guards for the post-#190 canonical-realizability audit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from post190_fb05_canonical_realizability import (
    EXACT_TWIN_EXCLUDED_BY_IDENTITY,
    EXACT_TWIN_SURVIVES,
    LAYER_IDS,
    layer0_ambient_replay,
    layer1_source_channel_coupling,
    layer2_scalar_aperture,
)
from probe_post190_fb05_canonical_realizability_scope import canonical_realizability_schedule

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post190_fb05_canonical_realizability_v1.json"
POST190_FIXTURE = HERE / "fixtures" / "post189_fb05_joint_selector_separability_v1.json"
SELECTOR_FIXTURE = HERE / "fixtures" / "post187_fb05_q14_mixed_drift_selector_v1.json"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    header = f"blob {len(data)}\0".encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    post190_fixture = json.loads(POST190_FIXTURE.read_text(encoding="utf-8"))
    selector_fixture = json.loads(SELECTOR_FIXTURE.read_text(encoding="utf-8"))

    if fixture["schema_version"] != "POST190_FB05_CANONICAL_REALIZABILITY_FIXTURE_v1":
        raise AssertionError("canonical-realizability fixture schema drift")
    if fixture["claim_cap"] != "POST190_CANONICAL_REALIZABILITY_RESEARCH_ONLY":
        raise AssertionError("canonical-realizability claim cap drift")
    if fixture["base_main_sha"] != "48fb064a2664a10e8b5711dba7a5ebb0450ea826":
        raise AssertionError("post-#191 base/main provenance drift")
    if int(fixture["theorem_authority_pr"]) != 184:
        raise AssertionError("theorem authority drift")
    if int(fixture["research_authority_pr"]) != 190:
        raise AssertionError("research authority drift")
    if int(fixture["routing_sync_pr"]) != 191:
        raise AssertionError("routing synchronization provenance drift")
    if fixture["required_layer_ids"] != list(LAYER_IDS):
        raise AssertionError("canonical-realizability layer registry drift")
    if int(fixture["arb_precision_bits"]) != 384:
        raise AssertionError("canonical-realizability precision drift")

    locked_sources = (
        (POST190_FIXTURE, "post190_joint_fixture", "post190_joint_fixture_blob_sha"),
        (HERE / "post189_fb05_joint_selector_separability.py", "post190_joint_module", "post190_joint_module_blob_sha"),
        (SELECTOR_FIXTURE, "source_selector_fixture", "source_selector_fixture_blob_sha"),
        (HERE / "post187_fb05_q14_mixed_drift_selector.py", "source_selector_module", "source_selector_module_blob_sha"),
        (HERE / "canonical_source_arb.py", "canonical_source_module", "canonical_source_module_blob_sha"),
        (HERE / "post177_fb05_q13_fixed_unit_derivative.py", "fixed_unit_derivative_module", "fixed_unit_derivative_module_blob_sha"),
        (HERE / "post179_fb05_q13_correlation_preserving_derivative.py", "schur_geometry_module", "schur_geometry_module_blob_sha"),
        (HERE / "fixtures" / "post185_fb05_q13_remainder_drift_v1.json", "inherited_schedule_fixture", "inherited_schedule_fixture_blob_sha"),
        (HERE / "probe_post185_fb05_q13_remainder_drift_scope.py", "inherited_schedule_probe", "inherited_schedule_probe_blob_sha"),
        (HERE / "CCM_CANONICAL_OBJECT_MAP_v3.json", "canonical_object_map", "canonical_object_map_blob_sha"),
    )
    for path, name_key, sha_key in locked_sources:
        if fixture[name_key] != path.name:
            raise AssertionError(f"source path drift: {name_key}")
        if git_blob_sha(path) != fixture[sha_key]:
            raise AssertionError(f"source content drift: {path.name}")

    schedule = canonical_realizability_schedule(fixture)
    if schedule["primary_box_count"] != 6 or schedule["control_box_count"] != 5:
        raise AssertionError("inherited canonical-realizability schedule drift")
    if schedule["selected_target"] != fixture["selected_target"]:
        raise AssertionError("selected target drift")
    if any(bool(schedule["policy"][key]) for key in (
        "adaptive_center_movement_permitted",
        "new_q_n_parity_search_permitted",
        "selector_refit_permitted",
        "threshold_refit_permitted",
        "new_selector_features_permitted",
        "arb_overlap_counts_as_exact_equality",
        "bounded_search_failure_counts_as_exclusion",
    )):
        raise AssertionError("post-#190 anti-refit/search firewall regressed")

    l0 = layer0_ambient_replay(selector_fixture, post190_fixture)
    l1 = layer1_source_channel_coupling(post190_fixture)
    l2 = layer2_scalar_aperture(post190_fixture)
    if l0["classification"] != EXACT_TWIN_SURVIVES:
        raise AssertionError("Layer 0 no longer reproduces #190")
    if l1["classification"] != EXACT_TWIN_SURVIVES:
        raise AssertionError("Layer 1 source coupling unexpectedly kills #190")
    if l2["classification"] != EXACT_TWIN_EXCLUDED_BY_IDENTITY:
        raise AssertionError("Layer 2 no longer excludes the specific #190 witness")
    if l2["general_reflection_control"]["classification"] != EXACT_TWIN_SURVIVES:
        raise AssertionError("scalar-law general reflection adversarial control failed")

    print(json.dumps({
        "status": "PASS",
        "base_main_sha": fixture["base_main_sha"],
        "layer_count": len(LAYER_IDS),
        "primary_box_count": schedule["primary_box_count"],
        "control_box_count": schedule["control_box_count"],
        "layer0": l0["classification"],
        "layer1": l1["classification"],
        "layer2_specific": l2["classification"],
        "layer2_general_reflection": l2["general_reflection_control"]["classification"],
        "theorem_promotion": False,
        "rh_claim": False
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
