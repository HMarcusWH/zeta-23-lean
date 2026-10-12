#!/usr/bin/env python3
"""WP5 Arb sign certificate for a non-zeta prime-power-consistent K2 model.

Only the von Mangoldt coefficients at p=2,3 are altered.  At all powers
p**j the model uses b_p*log(p)/sqrt(p**j); so c4=c2/sqrt(2).
The genuine pole, archimedean, diagonal correction, source kernels and
cutoff membership remain unchanged.  This is a falsifier for generic
structural no-crossing claims, NOT a counterexample to RH or ζ.

The two rational apertures bracket a *transverse* positive-to-negative
K2-even sign change.  Odd positivity is certified at both endpoints only;
a whole-bracket odd lower bound and firstness are not claimed.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_mat, ctx, fmpq

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import canonical_source_arb as C

K = 2
Q = 3
EVEN = (1, -4, 6, -4, 1)
ODD = (-1, 2, 0, -2, 1)
A2 = Fraction(490463763049119, 10**15)
A3 = Fraction(607742075660039, 10**15)
POINTS = (Fraction(1295, 1000), Fraction(1296, 1000))


def arbq(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def rayleigh(mat: arb_mat, v: tuple[int, ...]) -> arb:
    return sum(v[i] * mat[i, j] * v[j]
               for i in range(2*K+1) for j in range(2*K+1)) / sum(c*c for c in v)


def modified_weight(q: int) -> arb:
    """Prime-power-consistent non-zeta coefficient Lambda_mod(q)/sqrt(q).

    The rational A2/A3 are the already square-root-weighted q=2/3
    coefficients. Every higher power of the same prime shares that base
    logarithmic prime coefficient, including q4=A2/sqrt(2).
    """
    if q < 2:
        return arb(0)
    for prime, base in ((2, A2), (3, A3)):
        n, exponent = q, 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        if n == 1 and exponent:
            return arbq(base) / (arb(prime).sqrt() ** (exponent-1))
    return C.von_mangoldt(q) / arb(q).sqrt()


def modified_matrix(L: arb) -> tuple[arb_mat, arb_mat]:
    cell = C.fixed_cell_membership(Q, L)
    if not cell["certified"]:
        raise ValueError("not strictly inside the fixed q<=3 cutoff cell")
    zeta = C.canonical_source_matrix(L, K, Q)
    rows = [[zeta[i, j] for j in range(2*K+1)] for i in range(2*K+1)]
    for q in range(2, Q + 1):
        old_c = C.von_mangoldt(q) / arb(q).sqrt()
        diff = old_c - modified_weight(q)
        if diff.is_zero():
            continue
        logq = arb(q).log()
        for i,n in enumerate(range(-K,K+1)):
            for j,m in enumerate(range(-K,K+1)):
                rows[i][j] += diff * C.q_basis(n,m,logq,L)
    return zeta, arb_mat(rows)


def eval_at(Lq: Fraction) -> dict:
    raw, model = modified_matrix(arbq(Lq))
    out = {"aperture":[Lq.numerator,Lq.denominator],
           "cutoff_Q":Q,"certified_cutoff_cell":True,"true":{},"modified":{}}
    for name,v in (("even",EVEN),("odd",ODD)):
        out["true"][name] = C.ball_record(rayleigh(raw,v),40)
        out["modified"][name] = C.ball_record(rayleigh(model,v),40)
    out["signs"] = {
        "modified_even_positive":bool(rayleigh(model,EVEN)>0),
        "modified_even_negative":bool(rayleigh(model,EVEN)<0),
        "modified_odd_positive":bool(rayleigh(model,ODD)>0),
        "true_even_positive":bool(rayleigh(raw,EVEN)>0),
    }
    return out


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--precision-bits",type=int,default=256)
    args=parser.parse_args()
    C.set_precision(args.precision_bits);ctx.prec=args.precision_bits
    # These model consistency checks are mathematical input to the falsifier,
    # not optional prose claims about coefficients outside the Q3 test window.
    model_checks = {
        "q4_equals_q2_over_sqrt2":
            bool((modified_weight(4) - modified_weight(2)/arb(2).sqrt()).contains(0)),
        "q8_equals_q4_over_sqrt2":
            bool((modified_weight(8) - modified_weight(4)/arb(2).sqrt()).contains(0)),
        "q9_equals_q3_over_sqrt3":
            bool((modified_weight(9) - modified_weight(3)/arb(3).sqrt()).contains(0)),
        "all_2_3_powers_positive":
            all(bool(modified_weight(q)>0) for q in (2,3,4,8,9)),
        "non_prime_power_six_is_zero":bool(modified_weight(6).is_zero()),
    }
    if not all(model_checks.values()):
        raise AssertionError(("invalid modified-prime power law", model_checks))
    samples=[eval_at(p) for p in POINTS]
    tests={
        "left_model_even_positive":samples[0]["signs"]["modified_even_positive"],
        "right_model_even_negative":samples[1]["signs"]["modified_even_negative"],
        "model_odd_positive_at_both_sample_endpoints":all(
            p["signs"]["modified_odd_positive"] for p in samples),
        "true_zeta_even_positive_at_both_sample_endpoints":all(
            p["signs"]["true_even_positive"] for p in samples),
        "same_exact_q3_cell":all(p["certified_cutoff_cell"] for p in samples),
    }
    good=all(tests.values())
    rec={"schema":"post287.wp5.arb-crossing.v1",
         "claim_status":"INTERVAL_EVIDENCE" if good else "UNRESOLVED",
         "terminal_claim":"RH_OPEN",
         "model_is_actual_zeta":False,
         "complete_canonical_pole_arch_and_wCorrection":True,
         "weights":{"a2":str(A2),"a3":str(A3),
                    "c4":"a2/sqrt(2) (prime-power consistency; not in q3 cell)"},
         "precision_bits":args.precision_bits,"samples":samples,"checks":tests,
         "model_consistency":model_checks,
         "not_claimed":["global first contact","odd positivity over whole bracket",
                        "universal canonical positivity","RH"]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(rec,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":rec["claim_status"],"checks":tests},sort_keys=True))
    return 0 if good else 1


if __name__=="__main__":
    raise SystemExit(main())
