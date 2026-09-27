from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    negative_pair = [Fraction(-1), Fraction(0)]
    positive_bulk = [Fraction(2), Fraction(2)]
    total = [a + b for a, b in zip(negative_pair, positive_bulk)]
    if min(total) <= 0:
        raise SystemExit("masking regression construction failed")
    out = {
        "schema_version": "RHRC-CLOSURE-TRACK-1.0",
        "track_id": "D",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": "PAIR_VISIBILITY_REQUIRES_BULK_CONTROL_MASKING_COUNTEREXAMPLE_CONFIRMED",
        "theorem_authority": False,
        "rh_closure": False,
        "terminal_claim": "RH_OPEN",
        "masking_counterexample": {
            "negative_pair_diagonal": [str(x) for x in negative_pair],
            "positive_bulk_diagonal": [str(x) for x in positive_bulk],
            "total_diagonal": [str(x) for x in total]
        }
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
