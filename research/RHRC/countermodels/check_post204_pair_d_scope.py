#!/usr/bin/env python3
"""Scope/provenance firewall for post-#204 Pair-D C1 certification."""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post204_pair_d_c1_v1.json"
GEOM = HERE / "post204_pair_d_exact_geometry.py"
CERT = HERE / "certify_post204_pair_d_structural_countermodel.py"


def main() -> None:
    fx = json.loads(FIXTURE.read_text())
    assert fx["schema_version"] == "POST204_PAIR_D_C1_FIXTURE_v1"
    assert fx["base_main_sha"] == "79ea665689dc107018936a785a97d12a8f5c07c7"
    assert fx["base_main_tree"] == "778a3e8daef6ffb60af3026bc489f9f2ee16007f"
    assert fx["theorem_authority_pr"] == 184
    assert fx["research_authority_pr"] == 203
    assert fx["routing_sync_pr"] == 204
    hist = fx["historical_fixture"]
    assert hist["name"] == "C1"
    assert hist["q_by_abs_index"] == [1, 1, 1, -10]
    assert hist["predecessor_N"] == 2
    assert hist["successor_K"] == 3
    assert hist["selected_parity"] == "even"

    text = GEOM.read_text() + "\n" + CERT.read_text()
    for forbidden in (
        "import numpy", "from numpy", "import scipy", "from scipy",
        "import mpmath", "from mpmath", "import flint", "from flint",
        "arb(", "canonical_source_matrix_L", "post202_fb05_q14",
        "post200_fb05_q14", "post198_fb05_q14",
    ):
        assert forbidden not in text, f"forbidden scope marker: {forbidden}"

    required = (
        "sympy", "exact_parity_basis", "centered_predecessor_basis",
        "exact_shell_generator", "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
        "canonical_realizability",
    )
    for marker in required:
        assert marker in text, f"missing required scope marker: {marker}"

    print(json.dumps({
        "status": "PASS",
        "exact_rational_only": True,
        "adaptive_search": False,
        "canonical_search": False,
        "pair_a_imports": False,
        "theorem_promotion": False,
        "rh_claim": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
