"""POST285 M09 regression: zero-endpoint weighted remainder identity (Steps 32, 96).

Checks the statements proved in `Zeta23/CCM/WeightedRemainderIdentity.lean`.
For a C^1 test h with h(0) = h(L) = 0 the zero-endpoint production value

    A_L[h] = int_0^L h (e^{-t/2} + e^{t/2}) - int_0^L h rho
             - sum_{2 <= q <= e^L} Lambda(q)/sqrt(q) h(log q),
    rho(t) = e^{t/2} / (e^t - e^{-t}),

equals

    int_0^L R(e^t) h'(t) dt + int_0^L (e^{-t/2} - rho(t)) h(t) dt,
    R(x) = sum_{n <= x} Lambda(n)/sqrt(n) - 2 sqrt(x).

The contact-weighted instance h(t) = t^2 e(1 - t/L) with e(0) = 0 is checked
with the Lean derivative h'(t) = 2t e(1 - t/L) - (t^2/L) e'(1 - t/L).  The
identity uses only C^1 regularity and e(0) = 0, so a synthetic smooth energy
e(s) = s (1 + s^2) cos(w s) stands in for the source energy e_{Dz}.

Apertures cover the prime-free range (L < log 2), the seam L = log 2, values
just after prime-power seams, and non-integer cutoffs.  Tests are complex.

Negative controls (each must FAIL by the predicted amount):
  C1  nonzero right endpoint h(L) != 0 (h(0) = 0 kept): miss = R(e^L) h(L);
  C2  main term dropped (S(e^t) in place of R(e^t)): miss = -int e^{t/2} h;
  C3  contact derivative without the chain-rule factor -1/L: nonzero miss.

Step 28 replay (Arb, python-flint): at K = 2, L = 1.2, z = (1,-4,6,-4,1),
Dz = (-2,4,0,-4,2), the historical float values E(Dz) ~ +0.21549446 and
A_L[t^2 e_{Dz}(1 - t/L)] ~ -0.52241963 are enclosed with certified signs.
E(Dz) is the M05 regularized value (theorem-equal to the canonical energy);
on [0, 1e-12] its archimedean integrand is bounded through |N(t)| <= t sup|N'|.
z is not an actual contact: the pair only certifies that positive ordinary odd
energy does not force a positive weighted value (gate G-WEIGHTED).

Regression evidence only; the identity carries no sign, and no bound on R is
used or claimed.
"""
from __future__ import annotations

import argparse
import json
import math

import mpmath as mp
from flint import acb, arb, ctx


def prime_base(n: int):
    """p if n = p^k (k >= 1), else None."""
    if n < 2:
        return None
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return p if m == 1 else None
        p += 1
    return n


def von_mangoldt(n: int):
    p = prime_base(n)
    return mp.log(p) if p is not None else mp.mpf(0)


def rho(t):
    return mp.e ** (t / 2) / (mp.e ** t - mp.e ** (-t))


def staircase(L):
    """Breakpoints log n (2 <= n <= e^L) and the cumulative weights S."""
    N = int(mp.floor(mp.e ** L))
    pts, S, acc = [], [], mp.mpf(0)
    for n in range(2, N + 1):
        lam = von_mangoldt(n)
        acc += lam / mp.sqrt(n)
        pts.append(mp.log(n))
        S.append(acc)
    return pts, S


def A_direct(h, L):
    pole = mp.quad(lambda t: h(t) * (mp.e ** (-t / 2) + mp.e ** (t / 2)), [0, L])
    arch = mp.quad(lambda t: h(t) * rho(t), [0, L])
    N = int(mp.floor(mp.e ** L))
    prime = mp.fsum(von_mangoldt(q) / mp.sqrt(q) * h(mp.log(q)) for q in range(2, N + 1))
    return pole - arch - prime


def remainder_side(h, hp, L, drop_main=False):
    pts, S = staircase(L)
    cuts = [mp.mpf(0)] + [p for p in pts if p < L] + [L]
    total = mp.mpf(0)
    for i in range(len(cuts) - 1):
        a, b = cuts[i], cuts[i + 1]
        if b <= a:
            continue
        s = S[i - 1] if i >= 1 else mp.mpf(0)
        if drop_main:
            total += mp.quad(lambda t: s * hp(t), [a, b])
        else:
            total += mp.quad(lambda t: (s - 2 * mp.e ** (t / 2)) * hp(t), [a, b])
    arch = mp.quad(lambda t: (mp.e ** (-t / 2) - rho(t)) * h(t), [0, L])
    return total + arch


def R_at(L):
    pts, S = staircase(L)
    return (S[-1] if S else mp.mpf(0)) - 2 * mp.e ** (L / 2)


def poly_test(L, coeffs):
    """h(t) = t (L - t) p(t), complex polynomial p."""
    def p(t):
        return mp.fsum(c * t ** k for k, c in enumerate(coeffs))

    def dp(t):
        return mp.fsum(k * c * t ** (k - 1) for k, c in enumerate(coeffs) if k)

    h = lambda t: t * (L - t) * p(t)
    hp = lambda t: (L - 2 * t) * p(t) + t * (L - t) * dp(t)
    return h, hp


def energy(w):
    e = lambda s: s * (1 + s * s) * mp.cos(w * s)
    de = lambda s: (1 + 3 * s * s) * mp.cos(w * s) - w * s * (1 + s * s) * mp.sin(w * s)
    return e, de


# ---------------------------------------------------------------------------
# Step 28 replay with Arb enclosures
# ---------------------------------------------------------------------------

def _arb_source_energy(om, u, idx, PI):
    tot = acb(0)
    for a, n in enumerate(idx):
        for b, m in enumerate(idx):
            if u[a] == 0 or u[b] == 0:
                continue
            if n == m:
                ent = 2 * om * (2 * PI * n * om).cos()
            else:
                ent = ((2 * PI * n * om).sin() - (2 * PI * m * om).sin()) / (PI * (n - m))
            tot += u[a] * u[b] * ent
    return tot


def _arb_source_energy_deriv(om, u, idx, PI):
    tot = acb(0)
    for a, n in enumerate(idx):
        for b, m in enumerate(idx):
            if u[a] == 0 or u[b] == 0:
                continue
            if n == m:
                ent = 2 * (2 * PI * n * om).cos() - 4 * PI * n * om * (2 * PI * n * om).sin()
            else:
                ent = (2 * n * (2 * PI * n * om).cos() - 2 * m * (2 * PI * m * om).cos()) / (n - m)
            tot += u[a] * u[b] * ent
    return tot


def step28_certificate():
    ctx.prec = 128
    PI = acb.pi()
    K = 2
    L = arb("1.2")
    z = [1, -4, 6, -4, 1]
    Dz = [(i - K) * v for i, v in enumerate(z)]
    idx = list(range(-K, K + 1))
    e = lambda om: _arb_source_energy(om, Dz, idx, PI)
    de = lambda om: _arb_source_energy_deriv(om, Dz, idx, PI)
    N = int(math.floor(math.exp(1.2)))
    primes = [(q, arb(prime_base(q)).log() / arb(q).sqrt())
              for q in range(2, N + 1) if prime_base(q) is not None]
    # weighted value A_L[t^2 e_Dz(1 - t/L)]; h rho = t e(1 - t/L) e^{t/2} / (2 sinc(i t))
    h = lambda t: t * t * e(1 - t / L)
    pole = acb.integral(lambda t, an: h(t) * ((-t / 2).exp() + (t / 2).exp()), 0, L)
    arch = acb.integral(lambda t, an: t * e(1 - t / L) * (t / 2).exp()
                        / (2 * (acb(0, 1) * t).sinc()), 0, L)
    prime = acb(0)
    for q, w in primes:
        prime += w * h(acb(arb(q).log()))
    A = (pole - arch - prime).real
    # M05 regularized energy E(Dz)
    f = lambda t: e(1 - t / L)
    c = e(acb(1))
    pole_E = acb.integral(lambda t, an: f(t) * ((-t / 2).exp() + (t / 2).exp()), 0, L)
    delta = arb("1e-12")
    arch_main = acb.integral(lambda t, an: (f(t) - c * (-t / 2).exp()) * (t / 2).exp()
                             / (t.exp() - (-t).exp()), delta, L)
    ball = arb(delta / 2, delta / 2)
    nprime = (-de(acb(1 - ball / L)) / L) + c * (-acb(ball) / 2).exp() / 2
    head = arb(0, delta * abs(nprime).upper() * (delta / 2).exp() / 2)
    wcorr = (arb.const_euler() + (4 * arb.pi()).log()) / 2 - ((L.exp() + 1) / (L.exp() - 1)).log() / 2
    prime_E = acb(0)
    for q, w in primes:
        prime_E += w * f(acb(arb(q).log()))
    E = (pole_E - (arch_main + head) - c * wcorr - prime_E).real
    hist_E, hist_A = arb("0.21549446"), arb("-0.52241963")
    return {
        "K": K, "L": "1.2", "z": z, "Dz": Dz, "precision_bits": 128,
        "E_Dz": E.str(20, radius=True),
        "A_L_t2_e_Dz": A.str(20, radius=True),
        "E_Dz_certified_positive": bool(E > 0),
        "A_L_certified_negative": bool(A < 0),
        "historical_E_within_5e-9": bool(abs(E - hist_E) < arb("5e-9")),
        "historical_A_within_5e-9": bool(abs(A - hist_A) < arb("5e-9")),
        "label": "not an actual contact; certified discovery replay only",
    }


def check(tol: float):
    mp.mp.dps = 30
    Ls = [mp.mpf("0.5"), mp.log(2), mp.log(2) + mp.mpf("1e-9"), mp.mpf(1), mp.mpf("1.7"),
          mp.log(4) + mp.mpf("1e-9"), mp.mpf("2.3"), mp.log(7) + mp.mpf("1e-9"),
          mp.mpf(3), mp.mpf("4.2")]
    polys = [
        [mp.mpc(1, 0)],
        [mp.mpc("0.3", "-1.1"), mp.mpc("-0.7", "0.4"), mp.mpc("0.25", "0.9")],
        [mp.mpc("-1.3", "0.2"), mp.mpc(0, 0), mp.mpc("0.5", "-0.5"), mp.mpc("-0.1", "0.3")],
    ]
    rows = []
    worst = mp.mpf(0)
    for L in Ls:
        for j, c in enumerate(polys):
            h, hp = poly_test(L, c)
            lhs = A_direct(h, L)
            rhs = remainder_side(h, hp, L)
            res = abs(lhs - rhs) / max(mp.mpf(1), abs(lhs))
            worst = max(worst, res)
            rows.append({"L": float(L), "test": f"poly{j}", "A_L": [float(mp.re(lhs)), float(mp.im(lhs))],
                         "rel_residual": float(res)})
        for w in (mp.mpf("0.0"), mp.mpf("2.5")):
            e, de = energy(w)
            h = lambda t, e=e: t ** 2 * e(1 - t / L)
            hp = lambda t, e=e, de=de: 2 * t * e(1 - t / L) - t ** 2 / L * de(1 - t / L)
            lhs = A_direct(h, L)
            rhs = remainder_side(h, hp, L)
            res = abs(lhs - rhs) / max(mp.mpf(1), abs(lhs))
            worst = max(worst, res)
            rows.append({"L": float(L), "test": f"contact_w{float(w)}", "A_L": [float(lhs), 0.0],
                         "rel_residual": float(res)})
    # C1: nonzero right endpoint
    c1 = []
    c1_ok = True
    for L in (mp.mpf(1), mp.mpf("2.3"), mp.mpf(3)):
        h = lambda t: t * (1 + t)
        hp = lambda t: 1 + 2 * t
        miss = remainder_side(h, hp, L) - A_direct(h, L)
        pred = R_at(L) * h(L)
        c1_ok &= abs(miss - pred) < 1e-10 * max(1, abs(pred)) and abs(miss) > 1e-3
        c1.append({"L": float(L), "miss": float(miss), "predicted": float(pred)})
    # C2: main term dropped
    c2 = []
    c2_ok = True
    for L in (mp.mpf(1), mp.mpf(3)):
        h, hp = poly_test(L, polys[1])
        miss = remainder_side(h, hp, L, drop_main=True) - A_direct(h, L)
        pred = -mp.quad(lambda t: mp.e ** (t / 2) * h(t), [0, L])
        c2_ok &= abs(miss - pred) < 1e-10 * max(1, abs(pred)) and abs(miss) > 1e-3
        c2.append({"L": float(L), "miss": [float(mp.re(miss)), float(mp.im(miss))],
                   "predicted": [float(mp.re(pred)), float(mp.im(pred))]})
    # C3: chain-rule factor omitted
    c3 = []
    c3_fail = True
    for L in (mp.mpf("1.7"), mp.mpf(3)):
        e, de = energy(mp.mpf("2.5"))
        h = lambda t: t ** 2 * e(1 - t / L)
        hp_bad = lambda t: 2 * t * e(1 - t / L) + t ** 2 * de(1 - t / L)
        miss = remainder_side(h, hp_bad, L) - A_direct(h, L)
        c3_fail &= abs(miss) > 1e-3
        c3.append({"L": float(L), "miss": float(miss)})
    return {
        "dps": mp.mp.dps,
        "apertures": [float(L) for L in Ls],
        "cases": len(rows),
        "worst_relative_residual": float(worst),
        "identity_pass": worst < tol,
        "rows": rows,
        "control_C1_right_endpoint": c1,
        "control_C1_fails_by_R_eL_h_L": bool(c1_ok),
        "control_C2_main_term_dropped": c2,
        "control_C2_fails_by_exp_half_moment": bool(c2_ok),
        "control_C3_chain_rule_dropped": c3,
        "control_C3_fails": bool(c3_fail),
        "step28_replay": step28_certificate(),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--tol", type=float, default=1e-15)
    ap.add_argument("--output")
    args = ap.parse_args()
    res = check(args.tol)
    ok = (res["identity_pass"] and res["control_C1_fails_by_R_eL_h_L"]
          and res["control_C2_fails_by_exp_half_moment"] and res["control_C3_fails"]
          and res["step28_replay"]["E_Dz_certified_positive"]
          and res["step28_replay"]["A_L_certified_negative"]
          and res["step28_replay"]["historical_E_within_5e-9"]
          and res["step28_replay"]["historical_A_within_5e-9"])
    res["verdict"] = "PASS_REGRESSION" if ok else "FAIL"
    text = json.dumps(res, indent=2)
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text + "\n")
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}, indent=2))
    print("verdict:", res["verdict"])
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
