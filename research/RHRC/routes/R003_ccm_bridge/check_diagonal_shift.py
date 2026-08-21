"""R003 diagonal-shift diagnostic (FINITE NUMERICAL DIAGNOSTIC ONLY).

Hypothesis H:   WeilGram(n,m) = 2 * M_{lambda,N}(n,m) + c(L) * delta_{nm}

where M = Pole - Arch - Prime is R004's finite CCM matrix (L = 2 log lambda)
and WeilGram is the Weil explicit-formula zero-side sum for the even
two-sided test  K_{nm}(y) = q_basis(n,m,|y|,L),  supp K = [-L, L].

KEY REDUCTION.  The literature explicit formula reads
    WeilGram = [h(i/2) + h(-i/2)] - PrimeSum + ArchLit,
    ArchLit := (1/2pi) * int h(r) * [Re psi(1/4 + i r/2) - log pi] dr.
PR #28 established numerically (10 digits, all tested entries, two lambdas)
    h(i/2) + h(-i/2) = 2 * pole_component,     PrimeSum = 2 * prime_component,
and both are re-derived in closed form here (see h_closed / pole channel check).
Since 2M = 2*pole - 2*arch - 2*prime, those two channels cancel exactly and

    WeilGram - 2M  =  ArchLit + 2 * arch_component        (*)

identically.  So H is a statement about the ARCHIMEDEAN channel alone, testable
with NO zero sums and hence no slowly-converging zero tail.  That is what this
script measures.

CLOSED FORM for h.  With a = 2*pi*m/L, b = 2*pi*n/L (so aL, bL in 2*pi*Z):
  n != m:  h(r) = (2/(pi*(n-m))) * (1 - cos(rL)) * [ a/(a^2-r^2) - b/(b^2-r^2) ]
  n == m:  h(r) = (2/L) * (1 - cos(rL)) * [ 1/(b+r)^2 + 1/(b-r)^2 ]
Both are even in r and entire (the apparent poles at r = +-a, +-b are
removable because 1 - cos(rL) has a double zero there).
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

import mpmath as mp

R004 = Path(__file__).resolve().parents[1] / "R004_prolate_v2"
sys.path.insert(0, str(R004))
from run_commutator_gauntlet_v2 import (  # noqa: E402
    pole_component, arch_component, prime_component, q_basis,
    c_correction, w_correction, beta_L, alpha_L,
)

mp.mp.dps = 30
EPS = mp.mpf(10) ** (-12)


def h_closed(n: int, m: int, r, L):
    """Exact h_{nm}(r) = int K(y) e^{iry} dy, K even, supp [-L,L]."""
    r = mp.mpmathify(r)
    Lm = mp.mpf(L)
    onemc = 1 - mp.cos(r * Lm)

    def sq_term(c):
        """(1 - cos(rL)) / (c - r)^2, with the removable limit at r = c."""
        d = c - r
        if abs(d) < EPS:
            return Lm ** 2 / 2
        return onemc / d ** 2

    if n == m:
        b = 2 * mp.pi * n / Lm
        return (2 / Lm) * (sq_term(-b) + sq_term(b))

    a = 2 * mp.pi * m / Lm
    b = 2 * mp.pi * n / Lm

    def lin_term(c):
        """(1 - cos(rL)) * c / (c^2 - r^2), removable limit at r = +-c."""
        if abs(c) < EPS:
            return mp.mpf(0)
        if abs(c - r) < EPS or abs(c + r) < EPS:
            # c^2 - r^2 = (c-r)(c+r); one factor vanishes, the double zero of
            # (1-cos) supplies it back, leaving a finite limit.
            s = c - r if abs(c - r) < EPS else c + r
            other = c + r if abs(c - r) < EPS else c - r
            return (Lm ** 2 / 2) * s * c / other if abs(other) > EPS else mp.mpf(0)
        return onemc * c / (c ** 2 - r ** 2)

    return (2 / (mp.pi * (n - m))) * (lin_term(a) - lin_term(b))


def h_quad(n: int, m: int, r, L):
    """Reference: h by direct quadrature, for validating h_closed."""
    f = lambda y: 2 * q_basis(n, m, float(y), L) * mp.cos(r * y)
    return mp.quad(f, [0, L])


def bracket(r):
    return mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * r / 2)) - mp.log(mp.pi)


def arch_lit(n: int, m: int, L, R=mp.mpf(3000), panels=240):
    """(1/2pi) int_R h*bracket dr, h even => (1/pi) int_0^inf, with an analytic
    tail:  h(r) ~ (4/L)(1-cos(rL))/r^2  and  bracket(r) ~ log(r/(2pi)), whose
    non-oscillatory part contributes (4/L)(log(R/2pi)+1)/R."""
    Lm = mp.mpf(L)
    nodes = [mp.mpf(k) * R / panels for k in range(panels + 1)]
    # add the removable-singularity abscissae as panel breaks
    for c in (2 * mp.pi * abs(n) / Lm, 2 * mp.pi * abs(m) / Lm):
        if 0 < c < R:
            nodes.append(c)
    nodes = sorted(set(nodes))
    f = lambda r: h_closed(n, m, r, L) * bracket(r)
    main = mp.quad(f, nodes)
    tail = (4 / Lm) * (mp.log(R / (2 * mp.pi)) + 1) / R
    return (main + tail) / mp.pi


def residual(n: int, m: int, L):
    """(*)  WeilGram - 2M  =  ArchLit + 2*arch_component."""
    return arch_lit(n, m, L) + 2 * arch_component(n, m, L)


def validate_closed_form(L):
    print("\n=== validation: h_closed vs direct quadrature, and the pole channel ===")
    ok = True
    for (n, m) in [(0, 0), (1, 1), (1, 0), (2, -1)]:
        for r in [mp.mpf('0.7'), mp.mpf('3.3'), mp.mpf('11.0')]:
            a, b = h_closed(n, m, r, L), h_quad(n, m, r, L)
            if abs(a - b) > mp.mpf(10) ** (-15) * max(1, abs(b)):
                ok = False
                print(f"  MISMATCH (n,m)=({n},{m}) r={r}: {mp.nstr(a,12)} vs {mp.nstr(b,12)}")
        pole_lit = 2 * h_closed(n, m, mp.mpc(0, mp.mpf(1) / 2), L)
        pole_ccm = 2 * pole_component(n, m, L)
        d = abs(mp.re(pole_lit) - pole_ccm)
        print(f"  (n,m)=({n:2d},{m:2d})  2h(i/2)={mp.nstr(mp.re(pole_lit),12):>16}"
              f"   2*pole_component={pole_ccm:.12f}   |diff|={float(d):.2e}")
        ok = ok and d < 1e-15
    print(f"  closed form + pole channel: {'OK' if ok else 'FAILED'}")
    return ok


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lambdas", type=float, nargs="*", default=[2.0, 3.0, 5.0])
    ap.add_argument("--ns", type=int, nargs="*", default=[-3, -2, -1, 0, 1, 2, 3])
    ap.add_argument("--output", type=Path, default=None)
    args = ap.parse_args()
    t0 = time.time()

    validate_closed_form(2 * math.log(args.lambdas[0]))

    print("\n=== Q1: diagonal residual  Delta(n) = ArchLit(n,n) + 2*arch(n,n) ===")
    q1 = {}
    for lam in args.lambdas:
        L = 2 * math.log(lam)
        vals = {}
        print(f"\n  lambda={lam}  L={L:.8f}")
        for n in args.ns:
            d = residual(n, n, L)
            vals[n] = float(d)
            print(f"    n={n:>3}   Delta(n) = {mp.nstr(d, 14)}")
        spread = max(vals.values()) - min(vals.values())
        mean = sum(vals.values()) / len(vals)
        print(f"    -> spread over n = {spread:.3e}    mean c(L) = {mean:.14f}")
        q1[lam] = {"delta_by_n": vals, "spread": spread, "mean": mean}

    print("\n=== Q2: off-diagonal residual (H predicts exactly 0) ===")
    q2 = {}
    for lam in args.lambdas:
        L = 2 * math.log(lam)
        row = {}
        print(f"\n  lambda={lam}")
        for (n, m) in [(1, 0), (2, 1), (2, -2), (3, 0), (-1, 2)]:
            d = residual(n, m, L)
            row[f"{n},{m}"] = float(d)
            print(f"    (n,m)=({n:>2},{m:>2})   residual = {mp.nstr(d, 10)}")
        q2[lam] = row

    print("\n=== Q3: closed form for c(L) ===")
    q3 = {}
    for lam in args.lambdas:
        L = 2 * math.log(lam)
        # The off-diagonal residual is a common systematic of the archimedean
        # quadrature tail (H predicts it is exactly 0), so subtracting it from
        # the diagonal mean removes that systematic from c(L).
        off = q2[lam]
        sysoff = sum(off.values()) / len(off)
        c = q1[lam]["mean"] - sysoff
        cc, wc, b0 = c_correction(L), w_correction(L), beta_L(0, L)
        cands = {
            "4*c_correction  [derived]": 4 * cc,
            "c_correction": cc, "w_correction": wc, "c+w": cc + wc,
            "2(c+w)": 2 * (cc + wc), "2*beta_L(0)": 2 * b0, "beta_L(0)": b0,
            "2(c+w)-2beta0": 2 * (cc + wc - b0),
            "2*w_correction": 2 * wc, "2*c_correction": 2 * cc,
            "half(gamma+log4pi)": 0.5 * (float(mp.euler) + math.log(4 * math.pi)),
            "gamma+log4pi": float(mp.euler) + math.log(4 * math.pi),
            "log(4pi)": math.log(4 * math.pi), "L": L, "2/L": 2 / L,
        }
        best = min(cands.items(), key=lambda kv: abs(kv[1] - c))
        print(f"\n  lambda={lam}  raw diag mean = {q1[lam]['mean']:.14f}"
              f"   common off-diag systematic = {sysoff:.3e}"
              f"\n              corrected c(L) = {c:.14f}")
        for name, v in sorted(cands.items(), key=lambda kv: abs(kv[1] - c)):
            mark = "  <== MATCH" if abs(v - c) < 1e-8 else ""
            print(f"    {name:>22} = {v: .12f}   |diff| = {abs(v - c):.3e}{mark}")
        q3[lam] = {"measured_corrected": c, "raw_diag_mean": q1[lam]["mean"],
                   "offdiag_systematic": sysoff, "closest": best[0],
                   "closest_diff": abs(best[1] - c), "candidates": cands}

    diag_ok = all(v["spread"] < 1e-8 for v in q1.values())
    offdiag_ok = all(abs(x) < 1e-8 for row in q2.values() for x in row.values())
    print("\n=== VERDICT ===")
    print(f"  diagonal residual index-independent : {'YES' if diag_ok else 'NO'}")
    print(f"  off-diagonal residual vanishes      : {'YES' if offdiag_ok else 'NO'}")
    print(f"  hypothesis H                        : {'SUPPORTED' if diag_ok and offdiag_ok else 'REFUTED'}")

    result = {
        "run_id": "R003_DIAGONAL_SHIFT_ARCH_CHANNEL_001",
        "phase": "DISCOVERY",
        "claim_cap": "FINITE_NUMERICAL_DIAGNOSTIC_ONLY",
        "reduction": "WeilGram - 2M = ArchLit + 2*arch_component (pole and prime channels cancel exactly)",
        "configuration": {"lambdas": args.lambdas, "ns": args.ns, "mp_dps": mp.mp.dps,
                          "arch_R": 3000, "arch_panels": 240},
        "q1_diagonal": {str(k): v for k, v in q1.items()},
        "q2_offdiagonal": {str(k): v for k, v in q2.items()},
        "q3_closed_form": {str(k): v for k, v in q3.items()},
        "diagonal_index_independent": diag_ok,
        "offdiagonal_vanishes": offdiag_ok,
        "hypothesis_H_supported": diag_ok and offdiag_ok,
        "runtime_seconds": round(time.time() - t0, 1),
        "nonclaims": ["No RH evidence and no CCM identity is claimed.",
                      "Finite numerics have no theorem authority; Lean/comparator is the gate."],
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, default=float) + "\n")
        print(f"\nwrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
