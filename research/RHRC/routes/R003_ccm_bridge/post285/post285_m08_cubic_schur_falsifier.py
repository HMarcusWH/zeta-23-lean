"""POST285 M08 regression: abstract cubic Schur third derivative (Step 34).

Lean (Zeta23/CCM/AbstractCubicSchur.lean) proves, for C^3 families a(t), b(t),
H(t) with H(t0) invertible, R = H(t0)^-1 and b(t0) = 0, that the Schur scalar
s(t) = a(t) - <b(t), H(t)^-1 b(t)> has

    s'''(t0) = a''' - 3<b', R b''> - 3<b'', R b'> + 6<b', R H' R b'>,

and, for symmetric H(t0), with the response w = -R b' (H w = -b'):

    s'''(t0) = a''' - 6<b', R b''> + 6<R b', H' R b'> = a''' + 6<b'', w> + 6<H' w, w>.

It also proves the necessary sign: a zero of order three that turns negative to
the right has s'''(t0) <= 0.

This script checks the formulas exactly (SymPy rationals, s'''(t0) read off the
exact Taylor expansion of s(t) to order three, with H(t)^-1 expanded by the
Neumann series around H(t0)) on seeded symmetric
families with complement dimension 1..4, including the 2x2 Schur toy model
(dimension 1), and on complex Hermitian families of dimension 1..2 with the real-part form
s''' = a''' - 6 Re(b'* R b'') + 6 b'* R H' R b'.

Negative controls (must fail):
  C1  replacing the coefficient 6 of the <b', R H' R b'> term by 3;
  C2  dropping the hypothesis b(t0) = 0 (adding a constant b0 != 0);
  C3  the sign corollary: a family with s = s' = s'' = 0 and s''' > 0 is
      positive just to the right (no first-negative crossing), and one with
      s''' < 0 is negative there.

REGRESSION ONLY.  Abstract finite-dimensional calculus; nothing here is about
the arithmetic third derivative (gated on moving-aperture C^3 transport), the
canonical operator, contacts or RH.
"""
from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

import sympy as sp

t = sp.Symbol("t", real=True)


def rand_rat(rng, lo=-4, hi=4):
    return sp.Rational(rng.randint(lo * 6, hi * 6), 6)


def rand_vec(rng, n, cplx=False):
    if cplx:
        return sp.Matrix([rand_rat(rng) + sp.I * rand_rat(rng) for _ in range(n)])
    return sp.Matrix([rand_rat(rng) for _ in range(n)])


def rand_sym(rng, n, cplx=False):
    M = sp.zeros(n, n)
    for i in range(n):
        M[i, i] = rand_rat(rng)
        for j in range(i + 1, n):
            v = rand_rat(rng) + (sp.I * rand_rat(rng) if cplx else 0)
            M[i, j] = v
            M[j, i] = sp.conjugate(v)
    return M


def family(rng, n, cplx=False, b0=None):
    H0 = rand_sym(rng, n, cplx)
    # rational diagonal shift above the Gershgorin radius: positive definite
    H0 = H0 + (sum(abs(sp.re(x)) + abs(sp.im(x)) for x in H0) + 1) * sp.eye(n)
    H1, H2, H3 = (rand_sym(rng, n, cplx) for _ in range(3))
    b1, b2, b3 = (rand_vec(rng, n, cplx) for _ in range(3))
    a1, a2, a3 = (rand_rat(rng) for _ in range(3))
    H = H0 + t * H1 + t ** 2 / 2 * H2 + t ** 3 / 6 * H3
    b = t * b1 + t ** 2 / 2 * b2 + t ** 3 / 6 * b3
    if b0 is not None:
        b = b + b0
    a = a1 * t + a2 * t ** 2 / 2 + a3 * t ** 3 / 6
    return dict(H0=H0, H1=H1, b1=b1, b2=b2, a3=a3, H=H, b=b, a=a)


def truncate(expr_matrix, order=3):
    """Drop powers t^k, k > order, entrywise."""
    return expr_matrix.applyfunc(
        lambda e: sum(sp.expand(e).coeff(t, k) * t ** k for k in range(order + 1)))


def series_inverse(F, order=3):
    """H(t)^-1 to O(t^4) by the Neumann series around H0 (exact rationals)."""
    R0 = F["H0"].inv()
    X = truncate(R0 * (F["H"] - F["H0"]), order)
    n = X.shape[0]
    S, P = sp.eye(n), sp.eye(n)
    for _ in range(order):
        P = truncate(-P * X, order)
        S = S + P
    return truncate(S * R0, order)


def third_derivative(F):
    """s'''(0) = 6 [t^3] s(t), with s = a - b* H^-1 b expanded to O(t^4)."""
    Hinv = series_inverse(F)
    phi = sp.expand((F["b"].H * Hinv * F["b"])[0])
    s = sp.expand(F["a"] - phi)
    return sp.nsimplify(6 * s.coeff(t, 3)), s


def formulas(F, coeff=6):
    R = F["H0"].inv()
    b1, b2, H1 = F["b1"], F["b2"], F["H1"]
    general = F["a3"] - 3 * (b1.H * R * b2)[0] - 3 * (b2.H * R * b1)[0] + coeff * (b1.H * R * H1 * R * b1)[0]
    real_form = F["a3"] - 6 * sp.re((b1.H * R * b2)[0]) + coeff * (b1.H * R * H1 * R * b1)[0]
    w = -R * b1
    response = F["a3"] + 6 * sp.re((b2.H * w)[0]) + coeff * (w.H * H1 * w)[0]
    return [sp.nsimplify(sp.expand(x)) for x in (general, real_form, response)]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=3)
    ap.add_argument("--nmax", type=int, default=4)
    ap.add_argument("--ncmax", type=int, default=2)
    ap.add_argument("--seed", type=int, default=20261011)
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    rows = []
    c1_fail = c2_fail = real_families = 0

    def zero(x):
        return sp.expand(x) == 0

    # real symmetric families up to nmax; complex Hermitian ones up to ncmax
    for cplx, nmax in ((False, args.nmax), (True, args.ncmax)):
        for n in range(1, nmax + 1):
            for _ in range(args.trials):
                F = family(rng, n, cplx)
                s3, _ = third_derivative(F)
                g, r, w = formulas(F)
                g3, _, _ = formulas(F, coeff=3)
                ok = zero(s3 - g) and zero(s3 - r) and zero(s3 - w)
                c1 = not zero(s3 - g3)
                c1_fail += int(c1)
                if not cplx:
                    real_families += 1
                    Fb = family(rng, n, cplx, b0=rand_vec(rng, n) + sp.Matrix([1] + [0] * (n - 1)))
                    s3b, _ = third_derivative(Fb)
                    gb, _, _ = formulas(Fb)
                    c2_fail += int(not zero(s3b - gb))
                rows.append({"complex": cplx, "n": n, "s3": str(s3), "exact_match": bool(ok),
                             "C1_detects": bool(c1)})
    # C3: the sign corollary on the 2x2 toy model (n = 1), real
    sign_rows = []
    for target in (sp.Rational(1), sp.Rational(-1)):
        F = family(rng, 1)
        s3, s = third_derivative(F)
        # make s = s' = s'' = 0 at 0 by choosing a1, a2, then shift a3 to hit the target s'''
        s1 = sp.diff(s, t).subs(t, 0)
        s2 = sp.diff(s, t, 2).subs(t, 0)
        a = F["a"] - s1 * t - s2 * t ** 2 / 2 + (target - s3) * t ** 3 / 6
        s_poly = sp.expand(a - (F["b"].H * series_inverse(F) * F["b"])[0])
        d = [sp.factorial(k) * s_poly.coeff(t, k) for k in range(4)]

        def s_exact(x):
            Hx, bx = F["H"].subs(t, x), F["b"].subs(t, x)
            return a.subs(t, x) - (bx.H * Hx.inv() * bx)[0]
        right = [float(s_exact(sp.Rational(1, 10 ** k))) for k in (4, 5, 6)]
        sign_rows.append({"target_s3": str(target), "derivs_0_to_3": [str(x) for x in d],
                          "s_right": right,
                          "consistent": bool(d[0] == 0 and d[1] == 0 and d[2] == 0 and d[3] == target
                                             and all((x > 0) == (target > 0) for x in right))})
    summary = {
        "families": len(rows),
        "exact_matches": sum(r["exact_match"] for r in rows),
        "C1_coefficient_3_detected": c1_fail,
        "C2_nonzero_b0_detected": c2_fail,
        "C2_real_families": real_families,
        "C3_sign_consistent": all(r["consistent"] for r in sign_rows),
    }
    ok = summary["exact_matches"] == summary["families"] and summary["C3_sign_consistent"]
    controls = (summary["C1_coefficient_3_detected"] == summary["families"]
                and summary["C2_nonzero_b0_detected"] == real_families)
    disposition = "PASS_REGRESSION" if ok and controls else (
        "FAIL_IDENTITY" if not ok else "FAIL_CONTROLS_NOT_DISCRIMINATING")
    report = {"terminal_claim": "RH_OPEN", "authority": "REGRESSION_ONLY",
              "package": "M08_ABSTRACT_CUBIC_SCHUR", "disposition": disposition,
              "summary": summary, "rows": rows, "sign_rows": sign_rows}
    text = json.dumps(report, indent=2)
    if args.output:
        Path(args.output).write_text(text)
    print(json.dumps({k: v for k, v in report.items() if k not in ("rows",)}, indent=2))
    return 0 if disposition == "PASS_REGRESSION" else 1


if __name__ == "__main__":
    raise SystemExit(main())
