#!/usr/bin/env python3
"""Authoritative exact certificate for historical C1 as a Pair-D generic falsifier."""
from __future__ import annotations

import json

from post204_pair_d_exact_geometry import certify_c1, jsonable, load_fixture


def main() -> None:
    fx = load_fixture()
    rec = certify_c1()
    even = rec["even"]
    odd = rec["odd"]

    assert rec["reversal_symmetric"]
    assert rec["centered_index_commutator_zero"]
    assert even["predecessor_positive_definite"]
    assert odd["predecessor_positive_definite"]
    assert even["successor_bad_witness"]
    assert odd["successor_bad_witness"]
    assert rec["simultaneous_badness"]
    assert str(even["compressed_root"]) == fx["expected_exact_values"]["selected_even_root"]

    out = {
        "status": "PASS",
        "classification": "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
        "fixture": "C1",
        "predecessor_N": fx["historical_fixture"]["predecessor_N"],
        "successor_K": fx["historical_fixture"]["successor_K"],
        "selected_parity": "even",
        "even_predecessor_positive": True,
        "odd_predecessor_positive": True,
        "even_successor_bad": True,
        "odd_successor_bad": True,
        "selected_even_root": str(even["compressed_root"]),
        "even_witness_energy": str(even["quadratic_value"]),
        "odd_witness_energy": str(odd["quadratic_value"]),
        "reversal_symmetric": True,
        "centered_index_commutator_zero": True,
        "canonical_realizability": False,
        "canonical_source_implication": "NOT_TESTED",
        "theorem_promotion": False,
        "fb05_closed": False,
        "negative_root_exclusion": False,
        "rh_claim": False,
    }
    print(json.dumps(jsonable(out), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
