#!/usr/bin/env python3
"""Scope/provenance firewall for the post-#222 bi-regular zero-shift scalar audit."""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post222_fb05_biregular_zero_shift_scalar_v1.json"
BACKEND = HERE / "post222_fb05_biregular_zero_shift_scalar.py"
PROBE = HERE / "probe_post222_fb05_biregular_zero_shift_scalar_scope.py"
CERT = HERE / "certify_post222_fb05_biregular_zero_shift_scalar_scope.py"
INDEPENDENT = HERE / "check_post222_fb05_biregular_zero_shift_scalar_independent.py"


def main() -> None:
    fx = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert fx["schema_version"] == "POST222_FB05_BIREGULAR_ZERO_SHIFT_SCALAR_FIXTURE_v1"
    assert fx["base_main_sha"] == "001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5"
    assert fx["base_main_tree"] == "fd151afbcae3155cc4d32a75da08b6f7e0119099"
    assert fx["theorem_authority_pr"] == 222
    assert fx["validated_final_head_sha"] == "c46939488ead9535a63b547c38d64938a882a9f1"
    assert fx["merge_commit_sha"] == "001f375b4a7e70f69d2b7abb3bed1b9fd04f0ba5"
    assert fx["merge_tree"] == "fd151afbcae3155cc4d32a75da08b6f7e0119099"
    assert fx["latest_research_authority_pr"] == 215
    assert fx["selected_target"] == {
        "q_start": 13,
        "q_end": 15,
        "predecessor_N": 2,
        "successor_K": 3,
        "selected_parity": "even",
        "primary_Q": 14,
    }
    assert fx["selected_center_labels"] == [
        "Q13_midpoint",
        "Q14_left_of_determinant_basin",
        "Q14_determinant_basin",
        "Q14_right_of_determinant_basin",
        "Q15_midpoint",
    ]
    assert fx["whole_cell_ancestry"] == {
        "smaller_successor_K": 2,
        "predecessor_N_for_cover": 1,
        "parities": ["even", "odd"],
        "max_depth": 8,
    }
    assert fx["arb_precision_bits"] == 384
    assert fx["implementation_check_precision_bits"] == 192

    policy = fx["policy"]
    forbidden_true = (
        "new_q_search_permitted",
        "new_n_search_permitted",
        "parity_refit_permitted",
        "adaptive_point_search_permitted",
        "adaptive_center_movement_permitted",
        "target_sign_selection_permitted",
        "alpha_sign_selection_permitted",
        "gamma_sign_selection_permitted",
        "mu_sign_selection_permitted",
        "retained_state_refit_permitted",
        "adaptive_precision_increase_permitted",
        "theorem_promotion_permitted",
    )
    for key in forbidden_true:
        assert policy[key] is False, f"forbidden policy enabled: {key}"
    assert policy["adaptive_interval_bisection_permitted"] is True

    text = "\n".join(
        p.read_text(encoding="utf-8")
        for p in (BACKEND, PROBE, CERT, INDEPENDENT)
    )
    required = (
        "canonical_source_arb",
        "exact_parity_basis",
        "centered_predecessor_basis",
        "exact_shell_generator",
        "gauss_jordan_solve",
        "A.solve(b)",
        "explicit_source_moment_from_matrix",
        "transfer_residual",
        "transported_vector_residual",
        "adaptive_cell_cover",
        "certify_smaller_sizes",
        "CELL_MINIMAL_BIREGULAR_ALIGNED",
        "SIGMA_MINUS_NEGATIVE_CERTIFIED",
        "RIGOROUS_FINITE",
        "RH remains OPEN",
    )
    for marker in required:
        assert marker in text, f"missing required scope marker: {marker}"

    forbidden = (
        "scipy.optimize",
        "brentq",
        "minimize_scalar",
        "random.",
        "np.random",
        "adaptive_search",
        "selector_fit",
        "threshold_fit",
    )
    for marker in forbidden:
        assert marker not in text, f"forbidden scope marker: {marker}"

    print(json.dumps({
        "status": "PASS",
        "theorem_authority_pr": 222,
        "research_authority_pr": 215,
        "frozen_N": 2,
        "frozen_K": 3,
        "frozen_parity": "even",
        "frozen_center_count": 5,
        "whole_cell_smaller_K": 2,
        "whole_cell_parities": ["even", "odd"],
        "adaptive_point_search": False,
        "adaptive_interval_bisection": True,
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
