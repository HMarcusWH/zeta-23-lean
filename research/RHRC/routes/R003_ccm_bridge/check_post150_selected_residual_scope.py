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

    set_precision(160)
    L_arb = to_arb_rational(L_num, L_den)
    cell = fixed_cell_membership(Q, L_arb)
    if not cell["certified"]:
        raise AssertionError("dyadic smoke aperture escaped fixed cutoff cell")

    direct, rebuilt = channel_reconstruction(L_arb, 0, Q)
    delta = direct[0, 0] - rebuilt[0, 0]
    if not delta.contains(0):
        raise AssertionError("Arb direct/channel normalization reconstruction failed")

    fast00 = float(canonical_source_matrix_L(L_float, 0)[0, 0])
    arb_mid = float(direct[0, 0].mid())
    cross_backend_abs = abs(fast00 - arb_mid)
    if cross_backend_abs > 5e-8:
        raise AssertionError(f"fast/direct-Arb normalization mismatch: {cross_backend_abs}")

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
        "arb_smoke": {
            "cell_certified": cell["certified"],
            "direct_channel_reconstruction_contains_zero": True,
            "fast_midpoint_abs_difference": cross_backend_abs,
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
