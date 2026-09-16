#!/usr/bin/env python3
"""Implementation check for the exact post-#204 Pair-D C1 certificate."""
from __future__ import annotations

import json
from pathlib import Path

import sympy as sp

from post204_pair_d_exact_geometry import certify_c1, load_fixture


def main() -> None:
    fx = load_fixture()
    rec = certify_c1()
    exp = fx["expected_exact_values"]

    assert rec["status"] == "PASS"
    assert rec["reversal_symmetric"]
    assert rec["centered_index_commutator_zero"]
    assert rec["simultaneous_badness"]

    even = rec["even"]
    odd = rec["odd"]
    assert even["predecessor_positive_definite"]
    assert odd["predecessor_positive_definite"]
    assert even["predecessor_residual"] == sp.zeros(even["predecessor_basis"].cols, 1)
    assert odd["predecessor_residual"] == sp.zeros(odd["predecessor_basis"].cols, 1)
    assert even["compressed_root_residual"] == sp.zeros(even["successor_basis"].cols, 1)
    assert odd["compressed_root_residual"] == sp.zeros(odd["successor_basis"].cols, 1)

    assert str(even["predecessor_form"][0, 0]) == exp["even_predecessor_form"]
    assert str(odd["predecessor_form"][0, 0]) == exp["odd_predecessor_form"]
    assert str(even["quadratic_value"]) == exp["even_shell_energy"]
    assert str(odd["quadratic_value"]) == exp["odd_shell_energy"]
    assert str(even["norm_sq"]) == exp["even_shell_norm_sq"]
    assert str(odd["norm_sq"]) == exp["odd_shell_norm_sq"]
    assert str(even["compressed_root"]) == exp["selected_even_root"]

    print(json.dumps({
        "status": "PASS",
        "classification": rec["classification"],
        "even_predecessor_form": str(even["predecessor_form"][0, 0]),
        "odd_predecessor_form": str(odd["predecessor_form"][0, 0]),
        "even_quadratic_value": str(even["quadratic_value"]),
        "odd_quadratic_value": str(odd["quadratic_value"]),
        "selected_even_root": str(even["compressed_root"]),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
