from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True)
    args = ap.parse_args()
    raw = json.loads(Path(args.input).read_text())
    if raw.get("track_id") != "B" or raw.get("terminal_claim") != "RH_OPEN":
        raise SystemExit("wrong track/claim")
    for row in raw.get("cases", []):
        shell = Fraction(row["shell"])
        pred = Fraction(row["predecessor"])
        c2 = Fraction(row["coupling_sq"])
        d = shell * pred - c2
        if str(d) != row["determinant"] or (d >= 0) is not row["nonnegative"]:
            raise SystemExit(f"Schur recomputation mismatch: {row['id']}")
    if {r["id"] for r in raw["cases"]} != {
        "REGULAR_POSITIVE", "SINGULAR_BAD_COUPLING", "SINGULAR_ZERO_COUPLING"
    }:
        raise SystemExit("scope mismatch")
    print("CANONICAL SCHUR RESEARCH RECEIPT: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
