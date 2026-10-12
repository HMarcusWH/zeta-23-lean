#!/usr/bin/env python3
"""WP5: rigorous *modified-prime* K=2 transverse sign-control certificate.

The true production equation-(4.4) pole/archimedean/source terms are retained.
Only the three coefficient slots q=2,3,4 are modified.  In the rational
bracketing window [1.295,1.296], q=4 is not yet active.  We nevertheless
verify the exact q=4 relation so the source deformation remains a
prime-power-consistent adversarial family, not a fitted matrix.

The proof claim is finite and nonnative: opposite certified even scalar
signs at two rational apertures and positive odd scalars at both endpoints.
It does NOT certify global firstness or contradict RH.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx, fmpq

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import canonical_source_arb as source  # noqa: E402

BITS = 256
A2 = Fraction(490463763049119, 10**15)
A3 = Fraction(607742075660039, 10**15)
Z_EVEN = (1, -4, 6, -4, 1)
Z_ODD = (-1, 2, 0, -2, 1)
L_LEFT = Fraction(259, 200)   # 1.295
L_RIGHT = Fraction(162, 125)  # 1.296
ASSERTION_SCOPE = "NONNATIVE_K2_RATIONAL_TWO_ENDPOINT_SIGN_CONTROL"
TERMINAL_CLAIM = "RH_OPEN"


def fraction_ball(q: Fraction) -> arb:
    return arb(fmpq(q.numerator, q.denominator))


def scalar(M, v) -> arb:
    n2 = sum(t*t for t in v)
    return sum(v[i]*v[j]*M[i, j]
               for i in range(len(v)) for j in range(len(v))) / n2


def coefficients() -> dict[int, tuple[arb, arb]]:
    c2 = arb(2).log() / arb(2).sqrt()
    c3 = arb(3).log() / arb(3).sqrt()
    c4 = arb(2).log() / arb(4).sqrt()
    a2, a3 = fraction_ball(A2), fraction_ball(A3)
    a4 = a2 / arb(2).sqrt()
    # Verify prime-power consistency at q=4, with exact underlying rational a2.
    assert a4 * arb(2).sqrt() == a2 or (a4 * arb(2).sqrt() - a2).contains(0)
    return {2: (c2, a2), 3: (c3, a3), 4: (c4, a4)}


def modified_matrix(L: arb, Q: int, cs: dict[int, tuple[arb, arb]]):
    # Exact repaired source, including wCorrection once, with no legacy shift.
    true_matrix = source.canonical_source_matrix(L, 2, Q)
    rows = [[true_matrix[i, j] for j in range(5)] for i in range(5)]
    for q, (true_weight, modified_weight) in cs.items():
        if q > Q:
            continue
        correction = true_weight - modified_weight
        for i, n in enumerate(range(-2, 3)):
            for j, m in enumerate(range(-2, 3)):
                rows[i][j] += correction * source.q_basis(n, m, arb(q).log(), L)
    return type(true_matrix)(rows), true_matrix


def record(label: str, x: arb) -> dict:
    d = source.ball_record(x, digits=35)
    d["positive"] = bool(x > 0)
    d["negative"] = bool(x < 0)
    d["name"] = label
    return d


def certify() -> dict:
    source.set_precision(BITS)
    ctx.prec = BITS
    cs = coefficients()
    data = {
        "schema": "rh.post287.wp5.modified_prime.v1",
        "scope": ASSERTION_SCOPE,
        "terminal_claim": TERMINAL_CLAIM,
        "source": "canonical_source_arb:complete_eq44_matrix_with_modified_q2_q3_q4",
        "precision_bits": BITS,
        "coefficients": {
            "a2": [A2.numerator, A2.denominator],
            "a3": [A3.numerator, A3.denominator],
            "a4": "a2/sqrt(2)",
        },
        "points": [],
    }
    for aperture in (L_LEFT, L_RIGHT):
        L = fraction_ball(aperture)
        assert source.fixed_cell_membership(3, L)["certified"]
        Mmod, Mzeta = modified_matrix(L, 3, cs)
        data["points"].append({
            "L": [aperture.numerator, aperture.denominator],
            "Q": 3,
            "modified_even": record("modified_even", scalar(Mmod, Z_EVEN)),
            "modified_odd": record("modified_odd", scalar(Mmod, Z_ODD)),
            "zeta_even": record("zeta_even", scalar(Mzeta, Z_EVEN)),
            "zeta_odd": record("zeta_odd", scalar(Mzeta, Z_ODD)),
        })
    left, right = data["points"]
    assert left["modified_even"]["positive"], "left modified-even sign unresolved"
    assert right["modified_even"]["negative"], "right modified-even sign unresolved"
    assert left["modified_odd"]["positive"] and right["modified_odd"]["positive"], \
        "odd positivity was not certified at both endpoints"
    assert left["zeta_even"]["positive"] and right["zeta_even"]["positive"], \
        "true zeta positive control failed"
    data["disposition"] = "INTERVAL_EVIDENCE_MODIFIED_WEIGHTS_TRANSVERSE_SIGN_CHANGE"
    data["does_not_certify"] = [
        "globally first contact", "RH counterexample",
        "uniform finite-K negativity", "every aperture between the endpoints",
    ]
    return data


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    data = certify()
    text = json.dumps(data, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n")
    print(json.dumps({
        "scope": data["scope"], "disposition": data["disposition"],
        "precision_bits": data["precision_bits"], "terminal_claim": TERMINAL_CLAIM,
        "output": str(args.output) if args.output else None,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
