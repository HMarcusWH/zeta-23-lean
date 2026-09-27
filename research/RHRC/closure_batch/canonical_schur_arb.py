from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

from flint import ctx


FROZEN_Q = (13, 14, 15)
DEN = 8
PREC = 256


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    r003 = repo / "research" / "RHRC" / "routes" / "R003_ccm_bridge"
    sys.path.insert(0, str(r003))
    from post173_fb05_q13_scalar_barrier import (
        scalar_interval_record_arb,
        scalar_interval_json_record,
    )

    ctx.prec = PREC
    rows = []
    for Q in FROZEN_Q:
        for lo in range(DEN):
            rec = scalar_interval_record_arb(Q, lo, lo + 1, DEN)
            row = scalar_interval_json_record(rec)
            row["segment"] = {"lo": lo, "hi": lo + 1, "den": DEN}
            rows.append(row)

    selected = Counter(r["selected_classification"] for r in rows)
    scopes = Counter(r["scope_classification"] for r in rows)
    bad = [r for r in rows if r["selected_classification"] == "EVEN_BAD_INTERVAL_CERTIFIED"]
    out = {
        "schema_version": "RHRC-CLOSURE-CANONICAL-SCHUR-ARB-1.0",
        "claim_cap": "RIGOROUS_BOUNDED_ARB_RESEARCH",
        "adaptive_search": False,
        "precision_bits": PREC,
        "scope": {
            "Q": list(FROZEN_Q),
            "predecessor_N": 2,
            "successor_K": 3,
            "selected_parity": "even",
            "segments_per_cell": DEN,
        },
        "rows": rows,
        "selected_classification_counts": dict(selected),
        "scope_classification_counts": dict(scopes),
        "certified_bad_interval_count": len(bad),
        "classification": (
            "CANONICAL_SCHUR_BAD_INTERVALS_CERTIFIED_ON_FROZEN_SCOPE"
            if bad else "NO_CANONICAL_SCHUR_BAD_INTERVAL_CERTIFIED_ON_FROZEN_SCOPE"
        ),
        "theorem_promotion": False,
        "rh_claim": False,
        "terminal_claim": "RH_OPEN",
        "nonclaims": [
            "This bounded N=2/K=3 atlas does not prove or refute all-parameter CanonicalUniformDomination.",
            "A certified finite bad interval is a research falsifier for a universal domination conjecture only if the interval is in the theorem-aligned scope recorded here.",
        ],
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
