"""POST285 M71 regression: Andreief interior inertia of the parity carriers
(Steps 44 and 109).

Checks the statements proved in `Zeta23/CCM/CanonicalAndreiefInertia.lean`
for the elementary source matrix

    S_nm(omega) = (sin(2 pi n omega) - sin(2 pi m omega)) / (pi (n - m)),
    S_nn(omega) = 2 omega cos(2 pi n omega),

on the even and odd boundary-flat carriers of [-K, K], K = m + 2, in the
cosine-power bases

    e_k = (1 - latticeCos)^2 cos^k,     o_k = latticeSin (1 - latticeCos) cos^k,
    k = 0..m.

1. Certified leading-minor signs (python-flint Arb balls, adaptive precision):
   even D_r has sign (-1)^{r(r-1)/2}, odd D_r has sign (-1)^{r(r+1)/2}, for
   r = 1..K-1 and every omega on a grid in (0, 1/2].  A ball that does not
   exclude zero is reported as UNRESOLVED (the script then fails).
2. Jacobi count from the certified minors: even inertia (K/2, (K-1)/2, 0),
   odd inertia ((K-1)/2, K/2, 0).
3. Independent eigenvalue inertia (mpmath, 120 digits) on a sub-grid.
4. Gram identity: carrier Gram entries equal pi^{-1} int_0^a w(t) cos^k t
   w(a-t) cos^l(a-t) dt (even, w = (1-cos)^2) and minus the same with
   w = sin (1-cos) (odd), by mpmath quadrature.
Negative controls (must FAIL as predicted):
   C1. a > pi: on (1/2, 1) some certified leading-minor sign breaks the
       pattern (the M72 spectral-flow regime), so the hypothesis omega <= 1/2
       is not removable.
   C2. a > pi: the pair factor (cos q - cos p)(cos(a-q) - cos(a-p)) is
       positive for some p != q in [0, a].

Regression evidence only.  Nothing here concerns the canonical operator, its
contacts, or RH.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction

import mpmath as mp
from flint import arb, arb_mat, ctx


def lcos(f):
    keys = set()
    for n in f:
        keys.update({n - 1, n + 1})
    return {n: (f.get(n - 1, 0) + f.get(n + 1, 0)) / 2 for n in keys}


def lsin(f):
    keys = set()
    for n in f:
        keys.update({n - 1, n + 1})
    return {n: (f.get(n - 1, 0) - f.get(n + 1, 0)) / 2 for n in keys}


def l1mc(f):
    c = lcos(f)
    keys = set(f) | set(c)
    return {n: f.get(n, 0) - c.get(n, 0) for n in keys}


def cospow(k):
    f = {0: Fraction(1)}
    for _ in range(k):
        f = lcos(f)
    return f


def carrier_basis(m, parity):
    K = m + 2
    vecs = []
    for k in range(m + 1):
        q = cospow(k)
        f = l1mc(l1mc(q)) if parity == "even" else lsin(l1mc(q))
        vecs.append([f.get(n, Fraction(0)) for n in range(-K, K + 1)])
    return vecs


def arb_frac(x: Fraction):
    return arb(x.numerator) / x.denominator


def source_arb(om: Fraction, K: int):
    w = arb_frac(om)
    pi = arb.pi()
    rows = []
    for n in range(-K, K + 1):
        row = []
        for m in range(-K, K + 1):
            if n == m:
                row.append(2 * w * (2 * pi * n * w).cos())
            else:
                row.append(((2 * pi * n * w).sin() - (2 * pi * m * w).sin()) / (pi * (n - m)))
        rows.append(row)
    return arb_mat(rows)


def gram_arb(om, m, parity):
    K = m + 2
    U = carrier_basis(m, parity)
    S = source_arb(om, K)
    Ua = arb_mat([[arb_frac(x) for x in v] for v in U])  # rows = basis vectors
    return Ua * S * Ua.transpose()


def leading_minors(G):
    n = G.nrows()
    out = []
    for r in range(1, n + 1):
        sub = arb_mat([[G[i, j] for j in range(r)] for i in range(r)])
        out.append(sub.det())
    return out


def certified_signs(om, m, parity, precs=(512, 1024, 2048, 4096, 8192)):
    for p in precs:
        ctx.prec = p
        D = leading_minors(gram_arb(om, m, parity))
        signs = []
        ok = True
        for d in D:
            if d > 0:
                signs.append(1)
            elif d < 0:
                signs.append(-1)
            else:
                ok = False
                break
        if ok:
            return signs, p
    return None, precs[-1]


def expected_sign(r, parity):
    e = (r * (r - 1) // 2) % 2
    if parity == "odd":
        e = (e + r) % 2
    return -1 if e else 1


def jacobi_inertia(signs):
    prev = 1
    pos = neg = 0
    for s in signs:
        if s * prev > 0:
            pos += 1
        else:
            neg += 1
        prev = s
    return pos, neg


def mp_gram(om, m, parity):
    K = m + 2
    U = carrier_basis(m, parity)
    S = mp.matrix(2 * K + 1, 2 * K + 1)
    for i, n in enumerate(range(-K, K + 1)):
        for j, mm in enumerate(range(-K, K + 1)):
            if n == mm:
                S[i, j] = 2 * om * mp.cos(2 * mp.pi * n * om)
            else:
                S[i, j] = (mp.sin(2 * mp.pi * n * om) - mp.sin(2 * mp.pi * mm * om)) / (mp.pi * (n - mm))
    Um = mp.matrix([[mp.mpf(x.numerator) / x.denominator for x in v] for v in U])
    return Um * S * Um.T


def run(kmax: int):
    grid = [Fraction(1, 1000), Fraction(1, 200), Fraction(1, 50), Fraction(1, 20),
            Fraction(1, 10), Fraction(1, 8), Fraction(1, 6), Fraction(1, 5), Fraction(1, 4),
            Fraction(1, 3), Fraction(2, 5), Fraction(9, 20), Fraction(49, 100), Fraction(1, 2)]
    cells = []
    all_ok = True
    unresolved = 0
    for K in range(2, kmax + 1):
        m = K - 2
        for om in grid:
            for parity in ("even", "odd"):
                signs, prec = certified_signs(om, m, parity)
                if signs is None:
                    unresolved += 1
                    all_ok = False
                    cells.append({"K": K, "omega": str(om), "parity": parity, "status": "UNRESOLVED"})
                    continue
                exp = [expected_sign(r, parity) for r in range(1, m + 2)]
                pos, neg = jacobi_inertia(signs)
                n = m + 1
                exp_in = ((n + 1) // 2, n // 2) if parity == "even" else (n // 2, (n + 1) // 2)
                ok = signs == exp and (pos, neg) == exp_in
                all_ok &= ok
                cells.append({"K": K, "omega": str(om), "parity": parity, "prec_bits": prec,
                              "signs": signs, "inertia": [pos, neg, 0], "ok": ok})
    # 3. independent eigenvalue inertia
    mp.mp.dps = 120
    eig_cells = []
    eig_ok = True
    for K in range(2, min(kmax, 7) + 1):
        m = K - 2
        n = m + 1
        for om in (mp.mpf(1) / 20, mp.mpf(1) / 5, mp.mpf(1) / 3, mp.mpf(1) / 2):
            for parity in ("even", "odd"):
                G = mp_gram(om, m, parity)
                ev = mp.eigsy(G, eigvals_only=True)
                ev = [ev[i] for i in range(n)]
                scale = max(abs(x) for x in ev)
                pos = sum(1 for x in ev if x > scale * mp.mpf(10) ** -100)
                neg = sum(1 for x in ev if x < -scale * mp.mpf(10) ** -100)
                exp_in = ((n + 1) // 2, n // 2) if parity == "even" else (n // 2, (n + 1) // 2)
                ok = (pos, neg) == exp_in and pos + neg == n
                eig_ok &= ok
                eig_cells.append({"K": K, "omega": mp.nstr(om, 6), "parity": parity,
                                  "inertia": [pos, neg, n - pos - neg], "ok": ok})
    # 4. Gram identity by quadrature
    mp.mp.dps = 40
    quad = []
    quad_ok = True
    for (K, om) in ((3, mp.mpf(1) / 5), (4, mp.mpf(1) / 3), (5, mp.mpf(9) / 20), (4, mp.mpf(1) / 2)):
        m = K - 2
        a = 2 * mp.pi * om
        for parity in ("even", "odd"):
            G = mp_gram(om, m, parity)
            if parity == "even":
                w = lambda t: (1 - mp.cos(t)) ** 2
                sgn = 1
            else:
                w = lambda t: mp.sin(t) * (1 - mp.cos(t))
                sgn = -1
            worst = mp.mpf(0)
            for k in range(m + 1):
                for l in range(m + 1):
                    I = mp.quad(lambda t: w(t) * mp.cos(t) ** k * w(a - t) * mp.cos(a - t) ** l, [0, a])
                    worst = max(worst, abs(G[k, l] - sgn * I / mp.pi))
            ok = worst < mp.mpf(10) ** -25
            quad_ok &= ok
            quad.append({"K": K, "omega": mp.nstr(om, 6), "parity": parity,
                         "worst_abs_residual": mp.nstr(worst, 3), "ok": ok})
    # C1: beyond the half aperture some certified sign breaks the pattern
    c1_hits = []
    for K in range(3, kmax + 1):
        m = K - 2
        for om in (Fraction(3, 5), Fraction(7, 10), Fraction(4, 5), Fraction(9, 10), Fraction(19, 20)):
            for parity in ("even", "odd"):
                signs, prec = certified_signs(om, m, parity)
                if signs is None:
                    continue
                exp = [expected_sign(r, parity) for r in range(1, m + 2)]
                if signs != exp:
                    c1_hits.append({"K": K, "omega": str(om), "parity": parity, "signs": signs,
                                    "expected": exp})
    control_c1 = len(c1_hits) > 0
    # C2: pair sign positive for a > pi
    a = 1.5 * math.pi
    c2 = None
    for i in range(1, 200):
        for j in range(i + 1, 200):
            p, q = a * i / 200, a * j / 200
            v = (math.cos(q) - math.cos(p)) * (math.cos(a - q) - math.cos(a - p))
            if v > 1e-6:
                c2 = {"a": a, "p": p, "q": q, "pair_product": v}
                break
        if c2:
            break
    control_c2 = c2 is not None
    return {
        "kmax": kmax,
        "grid": [str(x) for x in grid],
        "certified_sign_cells": len(cells),
        "unresolved": unresolved,
        "certified_signs_pass": all_ok,
        "cells": cells,
        "eigen_inertia": eig_cells,
        "eigen_inertia_pass": eig_ok,
        "gram_identity": quad,
        "gram_identity_pass": quad_ok,
        "control_c1_beyond_half_aperture_breaks": control_c1,
        "control_c1_hits": c1_hits[:20],
        "control_c2_pair_sign_breaks_for_a_gt_pi": control_c2,
        "control_c2_witness": c2,
        "authority": "REGRESSION EVIDENCE ONLY; Lean theorem authority is CanonicalAndreiefInertia",
        "terminal_claim": "RH_OPEN",
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--kmax", type=int, default=9)
    ap.add_argument("--output")
    args = ap.parse_args()
    res = run(args.kmax)
    ok = (res["certified_signs_pass"] and res["eigen_inertia_pass"] and res["gram_identity_pass"]
          and res["control_c1_beyond_half_aperture_breaks"]
          and res["control_c2_pair_sign_breaks_for_a_gt_pi"])
    res["verdict"] = "PASS_REGRESSION" if ok else "FAIL"
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(json.dumps(res, indent=2) + "\n")
    print(json.dumps({k: v for k, v in res.items() if k not in ("cells", "eigen_inertia", "gram_identity", "control_c1_hits")}, indent=2))
    print("verdict:", res["verdict"])
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
