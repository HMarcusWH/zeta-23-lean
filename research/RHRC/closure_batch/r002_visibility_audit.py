from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    r002 = repo / "research" / "RHRC" / "routes" / "R002_multi_probe"
    sys.path.insert(0, str(r002))
    from compare_r002_ccm_probe_families import (
        q_basis,
        hard_character_correlation_closed,
        shifted_correlation_numeric,
    )

    L = 3.7
    cases = [
        (0, 0, 0.23 * L),
        (1, 0, 0.31 * L),
        (1, 1, 0.19 * L),
        (2, -1, 0.41 * L),
        (-2, 1, 0.67 * L),
    ]
    widths = (0.08, 0.17, 0.25)
    rows = []
    max_hard = 0.0
    max_smooth = 0.0
    for n, m, y in cases:
        q = q_basis(n, m, y, L)
        hard = hard_character_correlation_closed(n, m, y, L)
        max_hard = max(max_hard, abs(q - hard))
        smooth = []
        for frac in widths:
            value = shifted_correlation_numeric(
                n, m, y, L, taper_width=frac * L, steps=12000
            )
            residual = abs(q - value)
            max_smooth = max(max_smooth, residual)
            smooth.append({
                "taper_width_fraction": frac,
                "value": value,
                "qBasis_residual": residual,
            })
        rows.append({
            "n": n, "m": m, "y_over_L": y / L,
            "qBasis": q,
            "hard_closed": hard,
            "hard_residual": abs(q - hard),
            "smooth": smooth,
        })

    if max_hard > 5e-13:
        raise SystemExit(f"hard-window identity regression failed: {max_hard}")
    classification = (
        "SMOOTH_TAPER_SPECIALIZATION_BARRIER_CONFIRMED"
        if max_smooth > 1e-3
        else "SMOOTH_TAPER_DISTINCTION_UNRESOLVED"
    )
    out = {
        "schema_version": "RHRC-CLOSURE-R002-VISIBILITY-AUDIT-1.0",
        "claim_cap": "EXPERIMENTAL_SIGNAL_ONLY",
        "adaptive_search": False,
        "scope": {"L": L, "taper_width_fractions": list(widths)},
        "rows": rows,
        "max_hard_residual": max_hard,
        "max_smooth_residual": max_smooth,
        "classification": classification,
        "production_visibility_status": "OPEN_WINDOWED_MASKING_AND_CARRIER_T_CONTROL",
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
        "nonclaims": [
            "The generic smooth R002 family is not identified with the hard-window CCM qBasis.",
            "This audit does not prove production lambda<=1 visibility.",
            "Bulk masking, dynamic dimension d(T), and carrier T remain open.",
        ],
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
