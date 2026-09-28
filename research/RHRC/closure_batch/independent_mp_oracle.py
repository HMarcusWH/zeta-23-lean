from __future__ import annotations

import argparse
import cmath
import json
import math
from pathlib import Path


def f(z: complex) -> complex:
    return cmath.sin(math.pi * z)


def g(z: complex) -> complex:
    return f(z) * (z * z + 1)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    real_zero_residuals = {str(n): [abs(f(n)), abs(g(n))] for n in range(-4, 5)}
    at_i = {"f_abs": abs(f(1j)), "g_abs": abs(g(1j))}
    if max(max(v) for v in real_zero_residuals.values()) > 1e-12:
        raise SystemExit("real-zero regression failed")
    if not (at_i["f_abs"] > 1 and at_i["g_abs"] < 1e-12):
        raise SystemExit("complex-zero discriminator failed")
    out = {
        "schema_version": "RHRC-CLOSURE-TRACK-1.0",
        "track_id": "C",
        "execution_status": "SUCCESS",
        "integrity_status": "PASS",
        "research_disposition": "REAL_ZERO_MATCHING_FALSIFIED_AS_LIMIT_IDENTIFICATION_XI_IDENTIFICATION_OPEN",
        "theorem_authority": False,
        "rh_closure": False,
        "terminal_claim": "RH_OPEN",
        "real_zero_residuals": real_zero_residuals,
        "nonreal_discriminator_at_i": at_i
    }
    Path(args.output).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
