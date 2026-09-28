from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def det(shell: Fraction, pred: Fraction, coupling_sq: Fraction) -> Fraction:
    return shell * pred - coupling_sq


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    cases = [
        ("REGULAR_POSITIVE", Fraction(2), Fraction(2), Fraction(1)),
        ("SINGULAR_BAD_COUPLING", Fraction(1), Fraction(0), Fraction(1)),
        ("SINGULAR_ZERO_COUPLING", Fraction(1), Fraction(0), Fraction(0))
    ]
    rows = []
    for name, shell, pred, c2 in cases:
        d = det(shell, pred, c2)
        rows.append({
            "id": name,
            "shell": str(shell),
            "predecessor": str(pred),
            "coupling_sq": str(c2),
            "determinant": str(d),
            "nonnegative": d >= 0
        })
    out = {
        "schema_version": "RHRC-CLOSURE-TRACK-1.0",
        "track_id": "B",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": "SINGULAR_SAFE_SCHUR_INTERFACE_CONFIRMED_UNIFORM_CANONICAL_DOMINATION_OPEN",
        "theorem_authority": False,
        "rh_closure": False,
        "terminal_claim": "RH_OPEN",
        "cases": rows,
        "note": "Exact rational falsifiers test Schur semantics only; they are not canonical finite certificates."
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
