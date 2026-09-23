#!/usr/bin/env python3
"""Scope and semantics check for the frozen PR #247 global-bottom scout."""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures" / "post247_global_bottom_scout_v1.json"
BACKEND = HERE / "post247_global_bottom_scout.py"


def main() -> int:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    text = BACKEND.read_text(encoding="utf-8")

    expected = [
        ("Q13_midpoint", 13, 0.5),
        ("Q14_midpoint", 14, 0.5),
        ("Q15_midpoint", 15, 0.5),
    ]
    got = [
        (p["label"], int(p["Q"]), float(p["t"]))
        for p in fixture["frozen_points"]
    ]
    assert got == expected
    assert fixture["successor_K"] == 3
    assert fixture["predecessor_N"] == 2
    assert fixture["selection_head"] == "2a94647b25bf4e4c7dc9c94ef692cd48c1bd4674"
    assert fixture["policy"]["adaptive_search_permitted"] is False
    assert fixture["policy"]["threshold_refit_permitted"] is False
    assert fixture["policy"]["theorem_promotion_permitted"] is False
    assert "bad_regime" in fixture["observables"]
    assert "applicable_branch" in fixture["observables"]

    for forbidden in (
        "optimize.",
        "minimize(",
        "differential_evolution",
        "random.",
        "np.random",
    ):
        assert forbidden not in text

    assert "def classify_bottoms" in text
    assert 'applicable = "NONE"' in text

    print("POST247 GLOBAL BOTTOM SCOUT SCOPE: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
