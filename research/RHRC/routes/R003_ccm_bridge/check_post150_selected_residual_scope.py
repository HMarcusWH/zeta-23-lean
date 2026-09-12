#!/usr/bin/env python3
"""Cheap CI replay for the post-#150 selected-residual certification stack.

This is a plumbing/regression gate. It does not claim that FB-04 has found a
counterexample. Broad discovery stays out of the claim path; checked-in
rigorous candidates, if any, are replayed separately by the certificate tool.
"""
from __future__ import annotations

import json
from pathlib import Path

from canonical_source_arb import (
    channel_reconstruction,
    fixed_cell_membership,
    set_precision,
    to_arb_rational,
)
from canonical_source_numeric import canonical_source_matrix_L
from certify_post150_selected_residual_scope import certify_candidate
from post150_selected_residual import (
    evaluate_selected_residual_state,
    exact_geometry_self_check,
)

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post150_selected_residual_v1.json"


def main() -> int:
    geometry = exact_geometry_self_check(max_N=6)

    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture.get("schema_version") != "POST150_SELECTED_RESIDUAL_FIXTURE_v1":
        raise AssertionError("unexpected fixture schema")
    if not isinstance(fixture.get("candidates"), list):
        raise AssertionError("fixture candidates must be a list")

    Q = 2
    L_num, L_den = 3, 4
    L_float = L_num / L_den

    state = evaluate_selected_residual_state(Q, L_float, 2, "even")
    if state["flow"]["restricted_form_max_error"] > 2e-8:
        raise AssertionError("centered N-flow restricted-form regression")
    if state["selected_residual"]["identity_error"] > 2e-8:
        raise AssertionError("Schur/direct selected-residual identity regression")
    if state["selected_residual"]["channel_energies"]["reconstruction_error"] > 2e-8:
        raise AssertionError("fast canonical channel reconstruction regression")

    # Independent direct-production Arb normalization check on a nontrivial
    # three-by-three matrix, exercising diagonal and off-diagonal entries.
    set_precision(160)
    L_arb = to_arb_rational(L_num, L_den)
    cell = fixed_cell_membership(Q, L_arb)
    if not cell["certified"]:
        raise AssertionError("dyadic smoke aperture escaped fixed cutoff cell")

    direct, rebuilt = channel_reconstruction(L_arb, 1, Q)
    fast = canonical_source_matrix_L(L_float, 1)
    max_cross_backend_abs = 0.0
    for r in range(3):
        for c in range(3):
            delta = direct[r, c] - rebuilt[r, c]
            if not delta.contains(0):
                raise AssertionError(
                    f"Arb direct/channel normalization reconstruction failed at {(r, c)}"
                )
            midpoint_error = abs(float(direct[r, c].mid()) - float(fast[r, c]))
            max_cross_backend_abs = max(max_cross_backend_abs, midpoint_error)
    if max_cross_backend_abs > 5e-8:
        raise AssertionError(
            f"fast/direct-Arb normalization mismatch: {max_cross_backend_abs}"
        )

    # Exercise the *full* rigorous candidate path even though this smoke state
    # is not advertised as a counterexample. N=2 reaches the nontrivial
    # predecessor solve, Sylvester test, smaller-size ancestry audit, Schur
    # identity and channel reconstruction. Missing successor-badness witness is
    # intentional: the smoke must never be promoted to FB-04 evidence.
    rigorous_smoke = certify_candidate(
        {
            "Q": Q,
            "L_num": L_num,
            "L_den": L_den,
            "N": 2,
            "parity": "even",
            "expect_fb04_scoped_counterexample": False,
        },
        precision_bits=160,
    )
    if not rigorous_smoke["n_flow_restriction_agreement"]["certified_overlap_entrywise"]:
        raise AssertionError("rigorous N-flow restriction agreement failed")
    if not rigorous_smoke["predecessor"]["regular"]:
        raise AssertionError("rigorous smoke predecessor unexpectedly singular")
    if not rigorous_smoke["predecessor"]["positive_definite"]["certified"]:
        raise AssertionError("rigorous smoke predecessor positivity failed")
    if not rigorous_smoke["selected_residual"]["identity_overlap"]:
        raise AssertionError("rigorous Schur/direct selected-residual identity failed")
    if not rigorous_smoke["channels"]["reconstruction_overlap"]:
        raise AssertionError("rigorous channel reconstruction failed")
    if rigorous_smoke["fb04_scoped_counterexample_certified"]:
        raise AssertionError("non-counterexample smoke state was incorrectly promoted")

    payload = {
        "schema_version": "POST150_SELECTED_RESIDUAL_CI_CHECK_v1",
        "status": "PASS",
        "geometry_cases": len(geometry["checked"]),
        "fast_smoke": {
            "Q": Q,
            "L": L_float,
            "N": 2,
            "parity": "even",
            "flow_error": state["flow"]["restricted_form_max_error"],
            "schur_identity_error": state["selected_residual"]["identity_error"],
        },
        "arb_normalization_smoke": {
            "cell_certified": cell["certified"],
            "matrix_radius": 1,
            "direct_channel_reconstruction_entrywise": True,
            "max_fast_midpoint_abs_difference": max_cross_backend_abs,
        },
        "arb_full_candidate_path_smoke": {
            "predecessor_regular": rigorous_smoke["predecessor"]["regular"],
            "predecessor_positive_definite": rigorous_smoke["predecessor"]["positive_definite"]["certified"],
            "n_flow_overlap": rigorous_smoke["n_flow_restriction_agreement"]["certified_overlap_entrywise"],
            "schur_identity_overlap": rigorous_smoke["selected_residual"]["identity_overlap"],
            "channel_reconstruction_overlap": rigorous_smoke["channels"]["reconstruction_overlap"],
            "fb04_promoted": rigorous_smoke["fb04_scoped_counterexample_certified"],
        },
        "checked_in_candidate_count": len(fixture["candidates"]),
        "fb04_status": (
            "REPLAY_AVAILABLE" if fixture["candidates"] else "OPEN_NO_CHECKED_IN_CERTIFIED_COUNTEREXAMPLE"
        ),
        "claim_firewall": {"theorem_authority": False, "terminal_claim": "RH_OPEN"},
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
