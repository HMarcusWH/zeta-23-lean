#!/usr/bin/env python3
"""WP5 bounded Arb certificate for a non-zeta, prime-power-consistent K2 model.

Only the q=2 and q=3 von Mangoldt weights change. All genuine canonical
pole, archimedean and source-entry conventions are retained. At q=4 the
modified weight is exactly a2/sqrt(2), but q=4 is inactive inside the two
rational test apertures of the Q=3 cell.

Opposite certified even scalar signs yield a crossing by continuity.
Positive odd values at the *endpoints* are not a global firstness proof.
This executable never claims an actual zeta counterexample or RH.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_mat, ctx, fmpq

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import canonical_source_arb as C  # noqa: E402

EVEN = (1, -4, 6, -4, 1)
ODD = (-1, 2, 0, -2, 1)
A2 = Fraction(490463763049119, 10**15)
A3 = Fraction(607742075660039, 10**15)
POINTS = (Fraction(1295, 1000), Fraction(1296, 1000))
Q = 3
K = 2


def arbq(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def quad(mat: arb_mat, v: tuple[int, ...]) -> arb:
    return sum(v[i] * mat[i, j] * v[j]
               for i in range(2 * K + 1) for j in range(2 * K + 1)) / sum(t * t for t in v)


def modified_matrix(L: arb) -> tuple[arb_mat, arb_mat]:
    if not C.fixed_cell_membership(Q, L)["certified"]:
        raise ValueError("aperture not entirely inside fixed Q=3 cutoff cell")
    zeta = C.canonical_source_matrix(L, K, Q)
    rows = [[zeta[i, j] for j in range(2 * K + 1)] for i in range(2 * K + 1)]
    for q, new_c in ((2, arbq(A2)), (3, arbq(A3))):
        old_c = C.von_mangoldt(q) / arb(q).sqrt()
        diff = old_c - new_c
        y = arb(q).log()
        for i, n in enumerate(range(-K, K + 1)):
            for j, m in enumerate(range(-K, K + 1)):
                rows[i][j] += diff * C.q_basis(n, m, y, L)
    return zeta, arb_mat(rows)


def measured_point(t: Fraction) -> dict:
    L = arbq(t)
    real, mod = modified_matrix(L)
    got = {"L_num": t.numerator, "L_den": t.denominator, "Q": Q,
           "cell_certified": True, "true": {}, "modified": {}}
    for v, key in ((EVEN, "even"), (ODD, "odd")):
        got["true"][key] = C.ball_record(quad(real, v), 40)
        got["modified"][key] = C.ball_record(quad(mod, v), 40)
    got["checks"] = {
        "odd_positive": bool(quad(mod, ODD) > 0),
        "true_even_positive": bool(quad(real, EVEN) > 0),
        "modified_even_positive": bool(quad(mod, EVEN) > 0),
        "modified_even_negative": bool(quad(mod, EVEN) < 0),
    }
    return got


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    ap.add_argument("--precision-bits", type=int, default=256)
    args = ap.parse_args()
    C.set_precision(args.precision_bits)
    ctx.prec = args.precision_bits
    samples = [measured_point(x) for x in POINTS]
    tests = {
        "left_model_even_positive": samples[0]["checks"]["modified_even_positive"],
        "right_model_even_negative": samples[1]["checks"]["modified_even_negative"],
        "model_odd_positive_at_both_endpoints": all(x["checks"]["odd_positive"] for x in samples),
        "true_zeta_even_positive_at_both_endpoints": all(x["checks"]["true_even_positive"] for x in samples),
        "same_certified_cutoff_cell": all(x["cell_certified"] for x in samples),
    }
    data = {
        "package": "WP5_MODIFIED_PRIME_CROSSING",
        "terminal_claim": "RH_OPEN",
        "source": "actual equation-(4.4) CCM pole/arch matrix, altered von Mangoldt weights",
        "model_is_actual_zeta": False,
        "status": "INTERVAL_EVIDENCE" if all(tests.values()) else "UNRESOLVED",
        "precision_bits": args.precision_bits,
        "altered_atom_weights": {"q2_a2": str(A2), "q3_a3": str(A3),
                                 "q4_a2_over_sqrt2": "a2/sqrt(2)",
                                 "q4_in_bracket": False},
        "continuity_scope": "K=2 even scalar on the single open cutoff cell Q=3",
        "not_certified": ["odd-sector positivity at every interior aperture",
                          "firstness of the modified crossing", "genuine-zeta exclusion"],
        "samples": samples,
        "checks": tests,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"package": data["package"], "status": data["status"], "checks": tests}))
    return 0 if all(tests.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
