#!/usr/bin/env python3
"""WP0–WP7 preflight: source completeness and fail-closed implementation contract.

This runs with the Python standard library alone. It verifies paths, parses
EVERY new post287 Python program, and checks the accepted rev4 WP contract has
actual distinct source interfaces. It does not claim Lean correctness,
numerical validity or mathematical positivity. Independent compiler and Arb
gates must still pass.
"""
from __future__ import annotations

import ast
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / "research/RHRC/routes/R003_ccm_bridge/post287"
LEDGER = ROOT / "research/RHRC/integration/post287/OPEN_OBLIGATIONS.json"

PY = [
    "certificate_integrity.py",
    "wp2_literature_form_arb_probe.py",
    "wp2_k2_even_transcript.py",
    "wp2_verify_transcript.py",
    "wp2_wp4_normalization_gate.py",
    "wp4_k2_odd_prerequisite.py",
    "wp4_k3_frozen_q14_gate.py",
    "wp4_k3_fourth_order_fallback.py",
    "wp4_determinant_jet_exact_control.py",
    "wp4_fourth_order_validate.py",
    "wp4_k3_full_continuum.py",
    "wp4_k3_verify_full_transcript.py",
    "wp4_k3_assemble_shards.py",
    "wp5_modified_prime_crossing_certificate.py",
    "wp6_k2_signed_ray_probe.py",
]
LEAN = [
    "ReciprocalApertureConcavity.lean",
    "K2EvenBottomGluing.lean",
    "GlobalBottomStrictEvenShiftedRay.lean",
    "K3BottomWindowRecord.lean",
]
YAML = [
    "rhrc_post287_focused.yml",
    "rhrc_post287_numerical.yml",
    "rhrc_post287_wp6.yml",
    "rhrc_post287_wp4_full_continuum.yml",
]


def validate_focused_workflow(focused: str) -> None:
    """Require all theorem roots in the executable target loop and an actual lake build."""
    parts = focused.split("for target in ", 1)
    assert len(parts) == 2, "executable Lean build loop absent"
    body, marker, _ = parts[1].partition("\n          do")
    assert marker, "Lean target loop missing do clause"
    for name in LEAN:
        target = "Zeta23.CCM." + name[:-5]
        assert target in body.split(), ("missing Lean build target", name)
    assert 'if lake build "$target"; then' in focused, "Lean loop does not compile targets"

def check() -> dict:
    ledger = json.loads(LEDGER.read_text())
    assert ledger["terminal_claim"] == "RH_OPEN"
    assert ledger["requirements"]["D2"].startswith("FULL_K3")
    assert [p["id"] for p in ledger["packages"]] == [
        f"WP{i}" for i in range(8)
    ]
    crosswalk = (ROOT / "research/RHRC/integration/post287/"
                 "WP2_WP4_NORMALIZATION_CROSSWALK.md").read_text()
    for required in ("canonicalSourceMatrix", "sourceEq44GammaL",
                     "wCorrection", "Lambda", "nonunitary",
                     "interval", "prime"):
        if required == "Lambda":
            assert "von_mangoldt" in crosswalk
        elif required == "nonunitary":
            assert "nonunitary" in crosswalk
        else:
            assert required in crosswalk, ("missing normalization crosswalk", required)
    parsed = []
    for name in PY:
        file = BASE / name
        text = file.read_text()
        ast.parse(text, filename=str(file))
        parsed.append(name)

    for name in LEAN:
        file = ROOT / "Zeta23/CCM" / name
        source = file.read_text()
        assert "#print axioms" in source, name
        assert "\nsorry\n" not in source, name
        assert "\nadmit\n" not in source, name
        assert "\naxiom " not in source, name
        assert f"import Zeta23.CCM.{name[:-5]}" in (
            ROOT / "Zeta23/CCM.lean"
        ).read_text(), name

    focused = (ROOT / ".github/workflows" / YAML[0]).read_text()
    validate_focused_workflow(focused)
    workflow = (ROOT / ".github/workflows" / YAML[3]).read_text()
    assert "workflow_dispatch" in workflow
    assert "matrix:" in workflow
    assert "parity: ${{ fromJSON(needs.campaign-prerequisites.outputs.parities) }}" in workflow
    assert "parities=['even','odd']" in workflow
    assert "1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15" in workflow
    assert "wp4_k3_verify_full_transcript.py" in workflow
    assert "wp4_k3_assemble_shards.py" in workflow
    assert "timeout-minutes: 360" in workflow
    assert "workflow_call:" in workflow
    assert "needs: campaign-prerequisites" in workflow
    assert "--second-gate /tmp/wp4-prerequisites/second-gate.json" in workflow
    wrapper=(ROOT / '.github/workflows/rhrc_post284_source_inertia.yml').read_text()
    assert 'full_k3:' in wrapper and 'type: boolean' in wrapper
    assert "github.event_name == 'workflow_dispatch' && inputs.full_k3" in wrapper
    assert 'uses: ./.github/workflows/rhrc_post287_wp4_full_continuum.yml' in wrapper
    for name in YAML:
        assert (ROOT / ".github/workflows" / name).is_file(), name

    fallback = (BASE / "wp4_k3_fourth_order_fallback.py").read_text()
    continuum = (BASE / "wp4_k3_full_continuum.py").read_text()
    frozen = (BASE / "wp4_k3_frozen_q14_gate.py").read_text()
    assert "ORDER = 4" in fallback
    # Check actual Taylor code, not English adjectives in documentation.
    assert "def coeffs_of_a_and_delta" in fallback
    assert "range(1, ORDER)" in fallback
    assert "fourth_interval" in fallback
    assert "full_matrix_jets(interval,cutoff)" in fallback
    assert "Mi,Mpi,Mppi=M012" in continuum, (
        "second-order determinant bound must use full interval 0th, 1st and 2nd jets"
    )
    assert "Mi,Mpi,Mppi=jets(box,3,Q)" in frozen, (
        "frozen Q14 determinant curvature must enclose complete interval jets"
    )
    assert "dda*di+2*dai*ddi+ai*ddd" in frozen, (
        "frozen Q14 second derivative must use interval values, not centre values"
    )
    assert "d2a*di+2*dai*ddi+ai*d2d" in continuum, (
        "second-order determinant enclosure must use interval matrices"
    )
    # rev4: a passed frozen second-order gate does not license per-tile method switching.
    assert "if not result[\"accepted\"]" not in continuum
    assert 'result=evaluate((l,r),parity,cell,method)' in continuum
    assert 'if args.method=="FOURTH":' in continuum
    assert '"--fourth-gate"' in continuum
    assert '--method "$method" "${gate_args[@]}"' in workflow
    assert 'checker_receipt.json' in workflow
    assert '--output /tmp/wp4-k3-global/global_checker_receipt.json' in workflow
    assert "all_aperture_K3_positivity" in fallback
    assert "UNRESOLVED" in continuum
    glue = (ROOT / "Zeta23/CCM/K2EvenBottomGluing.lean").read_text()
    assert "k2EvenBottom_positive_of_M66_and_M51" in glue
    assert "hM51" in glue
    assert "k2OddBottom_positive_of_finite_window" in glue

    return {
        "schema": "post287.wp0_wp7.static_completeness.v1",
        "status": "SOURCE_SHAPES_PRESENT_NOT_COMPILER_VALIDATED",
        "python_ast_parsed": len(parsed),
        "lean_modules_wired": len(LEAN),
        "workflows_wired": len(YAML),
        "work_packages": 8,
        "K3_required_parities": ["even", "odd"],
        "K3_total_cutoff_cells": 15,
        "K3_required_computation_shards": 30,
        "K3_math_certificate_status": "OPEN_UNLESS_FULL_INTERVALS_ACCEPTED",
        "terminal_claim": "RH_OPEN",
        "does_not_establish": [
            "Lean compilation or permitted axiom set",
            "correctness of Arb operations",
            "true K3 positivity on full window",
            "RH",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(check(), sort_keys=True))
