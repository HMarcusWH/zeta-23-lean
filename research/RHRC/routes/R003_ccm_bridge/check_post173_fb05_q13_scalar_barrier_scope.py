#!/usr/bin/env python3
"""Deterministic acceptance checks for post-#173 q13 scalar-barrier tooling."""
from __future__ import annotations

import json

from flint import arb

from canonical_source_arb import set_precision
from post169_fb05_schur_visibility import one_step_geometry
from post173_fb05_q13_scalar_barrier import (
    PHYSICAL_QS,
    classify_selected_interval,
    physical_cell_midpoint,
    scalar_geometry,
    scalar_record_float,
    seam_overlap_record,
    zero_weight_inertness_record,
)


def _geometry_check() -> dict:
    rows = []
    for parity in ("even", "odd"):
        geom = one_step_geometry(2, parity)
        norms = scalar_geometry(parity)
        if geom.W_exact.cols != 1 or geom.step_basis_exact.cols != 2:
            raise AssertionError("q13 one-step dimension regression")
        if any(x != 0 for x in geom.W_exact.T * geom.c_exact):
            raise AssertionError("q13 predecessor/shell orthogonality regression")
        rows.append({
            "parity": parity,
            "predecessor_dim": geom.W_exact.cols,
            "successor_dim": geom.step_basis_exact.cols,
            "W_norm_sq": norms.W_norm_sq,
            "c_norm_sq": norms.c_norm_sq,
        })
    return {"status": "PASS", "rows": rows}


def _float_scalar_identity_check() -> list[dict]:
    rows = []
    for Q in PHYSICAL_QS:
        L = physical_cell_midpoint(Q)
        rec = scalar_record_float(L, "even")
        err = rec["pivot_identity_error"]
        if err is None or err > 2e-11:
            raise AssertionError(f"Delta2/a != generic Schur pivot at Q={Q}: {err}")
        rows.append({
            "Q": Q,
            "L": L,
            "a": rec["a"],
            "delta2": rec["delta2"],
            "generic_schur": rec["raw_schur_pivot"],
            "delta2_over_a": rec["pivot_from_delta_over_a"],
            "identity_error": err,
        })
    return rows


def _classifier_check() -> dict:
    cases = {
        "strict_positive": (arb(2), arb(3), "EVEN_STRICT_POSITIVE_CERTIFIED"),
        "strict_bad": (arb(2), arb(-3), "EVEN_BAD_INTERVAL_CERTIFIED"),
        "h1_loss": (arb(-2), arb(3), "EVEN_H1_LOSS_CERTIFIED"),
        "h1_contains_zero": (arb(0), arb(3), "EVEN_H1_UNRESOLVED"),
        "delta_contains_zero": (arb(2), arb(0), "EVEN_DETERMINANT_SIGN_UNRESOLVED"),
    }
    got = {}
    for name, (a, delta, expected) in cases.items():
        cls = classify_selected_interval(a, delta)
        got[name] = cls
        if cls != expected:
            raise AssertionError(f"classifier mismatch for {name}: {cls} != {expected}")
    return got


def main() -> int:
    set_precision(192)
    geometry = _geometry_check()
    scalar_identities = _float_scalar_identity_check()
    inert = zero_weight_inertness_record()
    if not inert["von_mangoldt_14_zero"] or not inert["von_mangoldt_15_zero"]:
        raise AssertionError("Q14/Q15 zero-von-Mangoldt inertness regression")

    seams = [seam_overlap_record(k) for k in (13, 14, 15, 16)]
    if not all(row["all_overlap"] for row in seams):
        raise AssertionError("q13 scalar seam continuation mismatch")

    classifier = _classifier_check()
    payload = {
        "schema_version": "POST173_FB05_Q13_SCALAR_BARRIER_CHECK_v1",
        "status": "PASS",
        "claim_cap": "EXACT_GEOMETRY_AND_DETERMINISTIC_METHOD_CHECK_ONLY",
        "geometry": geometry,
        "float_scalar_identities": scalar_identities,
        "zero_weight_inertness": inert,
        "seam_overlap_checks": seams,
        "synthetic_classifier": classifier,
        "checks": {
            "exact_q13_predecessor_successor_dimensions": True,
            "predecessor_shell_orthogonality": True,
            "Delta2_over_a_matches_generic_schur_at_safe_float_points": True,
            "Q14_Q15_von_mangoldt_weights_zero": True,
            "physical_threshold_continuations_overlap_at_13_14_15_16": True,
            "zero_containing_Delta2_is_unresolved_not_root_certified": True,
        },
        "nonclaims": [
            "Floating Delta2/a agreement is a deterministic implementation check, not a theorem.",
            "Seam overlap does not replace the piecewise Q=13/14/15 interval audit.",
            "An Arb interval containing zero is not a certified zero/contact point.",
            "No whole-cell sign is promoted by this checker.",
            "RH remains OPEN."
        ],
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
