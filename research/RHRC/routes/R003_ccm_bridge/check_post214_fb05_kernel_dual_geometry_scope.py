#!/usr/bin/env python3
"""Scope/provenance firewall for the post-#214 kernel dual-geometry audit."""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post214_fb05_kernel_dual_geometry_v1.json"
BACKEND = HERE / "post214_fb05_kernel_dual_geometry.py"
PROBE = HERE / "probe_post214_fb05_kernel_dual_geometry_scope.py"
CERT = HERE / "certify_post214_fb05_kernel_dual_geometry_scope.py"


def main() -> None:
    fx = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert fx["schema_version"] == "POST214_FB05_KERNEL_DUAL_GEOMETRY_FIXTURE_v1"
    assert fx["base_main_sha"] == "e073ecfc94c460a844097e9ed078f1da904bc26f"
    assert fx["base_main_tree"] == "15b37fdd230590f674e68a3ef9ac7bdb75f491b4"
    assert fx["theorem_authority_pr"] == 213
    assert fx["theorem_authority_head_sha"] == "703c3764a7d35aa4801e791a1929efa54c2533a1"
    assert fx["routing_sync_pr"] == 214
    assert fx["latest_research_authority_pr"] == 205
    assert fx["selected_target"] == {
        "q_start": 13,
        "q_end": 16,
        "predecessor_N": 2,
        "successor_K": 3,
        "selected_parity": "even",
        "primary_Q": 14,
    }
    assert fx["selected_center_labels"] == [
        "Q13_midpoint",
        "Q14_determinant_basin",
        "Q15_midpoint",
    ]
    assert fx["primary_center_label"] == "Q14_determinant_basin"
    assert fx["arb_precision_bits"] == 384
    assert fx["implementation_check_precision_bits"] == 192

    policy = fx["policy"]
    for key in (
        "new_q_n_k_parity_search_permitted",
        "adaptive_point_search_permitted",
        "adaptive_precision_increase_permitted",
        "component_sign_selection_permitted",
        "known_209_sign_import_permitted",
        "retained_state_refit_permitted",
        "riesz_same_observable_assumption_permitted",
        "theorem_promotion_permitted",
    ):
        assert policy[key] is False, f"forbidden policy enabled: {key}"

    text = BACKEND.read_text(encoding="utf-8") + "\n" + PROBE.read_text(encoding="utf-8")
    required = (
        "canonical_source_arb",
        "canonical_source_numeric",
        "exact_parity_basis",
        "TARGET_K = 3",
        'TARGET_PARITY = "even"',
        "dual_wedge",
        "generalized_extrema_2x2",
        "FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED",
        "DUAL_PROPORTIONALITY_NOT_FALSIFIED",
        "EXPERIMENTAL_SIGNAL_ONLY",
    )
    for marker in required:
        assert marker in text, f"missing required scope marker: {marker}"

    forbidden = (
        "scipy.optimize",
        "brentq",
        "random.",
        "np.random",
        "adaptive_search",
        "selector_fit",
        "threshold_fit",
        "sourceAtomRealEnergy",
        "canonicalPolePrimeRiesz",
    )
    for marker in forbidden:
        assert marker not in text, f"forbidden scope marker: {marker}"

    print(json.dumps({
        "status": "PASS",
        "frozen_K": 3,
        "frozen_parity": "even",
        "frozen_center_count": 3,
        "arb_precision_bits": 384,
        "adaptive_point_search": False,
        "adaptive_precision_increase": False,
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
