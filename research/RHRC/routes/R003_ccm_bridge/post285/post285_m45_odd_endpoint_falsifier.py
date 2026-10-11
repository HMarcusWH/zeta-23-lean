"""POST285 M45 regression: quantitative odd endpoint source bound (Step 82).

Checks the statements proved in `Zeta23/CCM/CanonicalSourceOddEndpointQuantitative.lean`
on the elementary source matrix

    S_nn = 2 w cos(2 pi n w),  S_nm = (sin(n a) - sin(m a)) / ((n - m) pi),  a = 2 pi w.

For a legal odd vector u (u_{-n} = -u_n, M_1(u) = 0) with m = |M_3(u)|,
B(u) = sum |n|^5 |u_n| and 0 <= w with (2 pi w)^2 B(u) <= 5 m, the theorem is

    Re e_u(w) <= -(pi^6/90) m^2 w^7.

The plan's angle theta(u) = (1/2pi) sqrt(5m / (A_K ||u||)), A_K^2 = 2 sum n^10,
is smaller than the B-angle because B(u) <= A_K ||u|| (Cauchy-Schwarz).

Certified part (Arb, python-flint, 256 bits): for Gaussian-integer legal odd
vectors with K = 2..8 (including the K = 2 generator (-1,2,0,-2,1)), at eight
rational apertures per vector up to the B-angle (the aperture hypothesis is
itself certified), the lower endpoint of -Re e_u(w) - (pi^6/90) m^2 w^7 is > 0.

Checks at 40 digits (mpmath): the fifth-order sine Taylor bound, the remainder
bound |T_u(t) + M_3 t^3/6| <= B |t|^5/120, the beta integral a^7/140, and the
ratio -e/((pi^6/90) m^2 w^7) tending to 16/7 as w -> 0 (the constant is sharp
up to the factor 16/7 coming from the 7/16 product bound).

Negative controls (each must FAIL as predicted):
  C1  constant (16/7)(1 + 1e-3) pi^6/90 in place of pi^6/90: fails at small w;
  C2  no aperture restriction: the K = 2 generator has e(1) = 20 > 0 (certified);
  C3  oddness dropped (M_1 = 0, M_3 != 0 kept, an even part with M_2 != 0
      added): Re e > 0 at small w, so the bound fails;
  C4  M_3 = 0 (K = 3 odd fifth-moment witness): -e/w^7 -> 0, so no positive
      w^7 lower bound exists without m > 0 (the theorem's bound is then 0).

Regression evidence only.  This is an elementary source statement; it is not a
sign of the canonical arithmetic test and not a contact or exclusion theorem.
"""
from __future__ import annotations

import argparse
import json
import random

import mpmath as mp
from flint import arb, ctx, fmpq

ctx.prec = 256
mp.mp.dps = 40


def legal_odd(K: int, rng: random.Random) -> list[complex]:
    """Gaussian-integer legal odd vector on -K..K (index n -> position n + K)."""
    v = {n: complex(rng.randint(-6, 6), rng.randint(-6, 6)) for n in range(2, K + 1)}
    v[1] = -sum(n * v[n] for n in range(2, K + 1))
    if K == 1 or all(x == 0 for x in v.values()):
        v[1] = 0
    u = [0j] * (2 * K + 1)
    for n in range(1, K + 1):
        u[K + n] = v[n]
        u[K - n] = -v[n]
    return u


def moment(K: int, u: list[complex], k: int) -> complex:
    return sum((i - K) ** k * u[i] for i in range(2 * K + 1))


def weight_B(K: int, u: list[complex]) -> float:
    return sum(abs(i - K) ** 5 * abs(u[i]) for i in range(2 * K + 1))


def arb_energy(K: int, u: list[complex], w: arb) -> arb:
    """Re sum conj(u_n) S_nm u_m in Arb (u Gaussian-integer)."""
    pi = arb.pi()
    a = 2 * pi * w
    sins = {n: (n * a).sin() for n in range(-K, K + 1)}
    total = arb(0)
    for i in range(2 * K + 1):
        n = i - K
        for j in range(2 * K + 1):
            m = j - K
            g = (u[i].conjugate() * u[j]).real
            if g == 0:
                continue
            if n == m:
                s = 2 * w * (2 * pi * n * w).cos()
            else:
                s = (sins[n] - sins[m]) / ((n - m) * pi)
            total += s * int(round(g))
    return total


def mp_energy(K: int, u: list[complex], w) -> mp.mpf:
    a = 2 * mp.pi * w
    total = mp.mpf(0)
    for i in range(2 * K + 1):
        n = i - K
        for j in range(2 * K + 1):
            m = j - K
            g = (complex(u[i]).conjugate() * complex(u[j])).real
            if g == 0:
                continue
            if n == m:
                s = 2 * w * mp.cos(2 * mp.pi * n * w)
            else:
                s = (mp.sin(n * a) - mp.sin(m * a)) / ((n - m) * mp.pi)
            total += s * g
    return total


def bound_coeff() -> arb:
    return arb.pi() ** 6 / 90


def certified_rows(vectors) -> tuple[list[dict], bool]:
    rows, ok = [], True
    for K, u in vectors:
        m2 = int(round(abs(moment(K, u, 3)) ** 2))
        m = arb(m2).sqrt()
        B = sum(abs(i - K) ** 5 * arb(int(round(abs(u[i]) ** 2))).sqrt() for i in range(2 * K + 1))
        thetaB = (5 * m / B).sqrt() / (2 * arb.pi())
        mid = float(thetaB.mid())
        for k in range(1, 9):
            w_q = fmpq(int(mid * k / 8 * 10 ** 12) - 1, 10 ** 12)
            w = arb(w_q)
            hyp = (2 * arb.pi() * w) ** 2 * B - 5 * m
            hyp_ok = bool(hyp < 0)
            e = arb_energy(K, u, w)
            gap = -e - bound_coeff() * m2 * w ** 7
            cert = bool(gap > 0)
            ratio = float((-e / (bound_coeff() * m2 * w ** 7)).mid())
            ok &= hyp_ok and cert
            rows.append({"K": K, "u": [[z.real, z.imag] for z in u], "M3_abs_sq": m2,
                         "omega": float(w_q.p) / float(w_q.q), "aperture_hypothesis_certified": hyp_ok,
                         "gap_certified_positive": cert, "ratio": ratio})
    return rows, ok


def taylor_checks(vectors) -> dict:
    worst_sin = mp.mpf(-1)
    for k in range(-400, 401):
        x = mp.mpf(k) / 37
        lhs = abs(mp.sin(x) - (x - x ** 3 / 6))
        rhs = abs(x) ** 5 / 120
        worst_sin = max(worst_sin, lhs - rhs)
    sin_ok = worst_sin <= 0
    worst_rem = mp.mpf(-1)
    for K, u in vectors:
        M3 = moment(K, u, 3)
        B = weight_B(K, u)
        for k in range(1, 41):
            t = mp.mpf(k) / 13
            T = sum(complex(u[i]) * mp.sin((i - K) * t) for i in range(2 * K + 1))
            R = T + mp.mpc(M3) * t ** 3 / 6
            worst_rem = max(worst_rem, abs(R) - mp.mpf(B) * t ** 5 / 120)
    rem_ok = worst_rem <= mp.mpf(10) ** -30
    beta = [abs(mp.quad(lambda t: t ** 3 * (a - t) ** 3, [0, a]) - a ** 7 / 140)
            for a in (mp.mpf("0.3"), mp.mpf(1), mp.mpf("2.7"))]
    beta_ok = max(beta) < mp.mpf(10) ** -30
    cs_ok = True
    for K, u in vectors:
        A = mp.sqrt(2 * sum(mp.mpf(n) ** 10 for n in range(1, K + 1)))
        A_direct = mp.sqrt(sum(mp.mpf(n) ** 10 for n in range(-K, K + 1)))
        nu = mp.sqrt(sum(abs(z) ** 2 for z in u))
        cs_ok &= weight_B(K, u) <= A * nu + 1e-20 and abs(A - A_direct) < 1e-30
    return {"sine_taylor_max_excess": float(worst_sin), "sine_taylor_ok": bool(sin_ok),
            "remainder_max_excess": float(worst_rem), "remainder_bound_ok": bool(rem_ok),
            "beta_integral_max_error": float(max(beta)), "beta_integral_ok": bool(beta_ok),
            "cauchy_schwarz_and_A_K_ok": bool(cs_ok)}


def small_omega_ratio(K, u) -> list[dict]:
    m2 = abs(moment(K, u, 3)) ** 2
    out = []
    for w in (mp.mpf("1e-2"), mp.mpf("1e-3"), mp.mpf("1e-4")):
        r = -mp_energy(K, u, w) / (mp.pi ** 6 / 90 * m2 * w ** 7)
        out.append({"omega": float(w), "ratio": float(r)})
    return out


def check() -> dict:
    rng = random.Random(45)
    k2 = [-1 + 0j, 2 + 0j, 0j, -2 + 0j, 1 + 0j]
    vectors = [(2, k2)]
    for K in range(2, 9):
        made = 0
        while made < 4:
            u = legal_odd(K, rng)
            if abs(moment(K, u, 3)) > 0:
                vectors.append((K, u))
                made += 1
    rows, cert_ok = certified_rows(vectors)
    taylor = taylor_checks(vectors)
    sharp = small_omega_ratio(2, k2)
    sharp_ok = abs(sharp[-1]["ratio"] - 16 / 7) < 1e-3

    # C1: constant (16/7)(1 + 1e-3) pi^6/90 fails at small omega.
    c1 = []
    c1_fail = False
    for K, u in vectors[:6]:
        m2 = abs(moment(K, u, 3)) ** 2
        w = mp.mpf("1e-4")
        e = mp_energy(K, u, w)
        strong = mp.mpf(16) / 7 * (1 + mp.mpf("1e-3")) * mp.pi ** 6 / 90 * m2 * w ** 7
        fails = -e < strong
        c1_fail |= bool(fails)
        c1.append({"K": K, "omega": float(w), "minus_e_over_strong": float(-e / strong), "fails": bool(fails)})

    # C2: without the aperture restriction the bound fails (K = 2 generator at omega = 1).
    e1 = arb_energy(2, k2, arb(1))
    c2 = {"omega": 1, "energy": float(e1.mid()), "energy_certified_positive": bool(e1 > 0),
          "exact_value": 20}
    c2_fail = bool(e1 > 0) and abs(float(e1.mid()) - 20) < 1e-30

    # C3: oddness dropped; even part (1,-2,2,-2,1) has M_0 = M_1 = M_3 = 0, M_2 = 4.
    mixed = [z + y for z, y in zip(k2, [1, -2, 2, -2, 1])]
    m2 = abs(moment(2, mixed, 3)) ** 2
    c3 = []
    c3_fail = False
    for w in (mp.mpf("1e-2"), mp.mpf("1e-3")):
        e = mp_energy(2, mixed, w)
        bound = -(mp.pi ** 6 / 90) * m2 * w ** 7
        fails = e > bound
        c3_fail |= bool(fails)
        c3.append({"omega": float(w), "energy": float(e), "claimed_upper_bound": float(bound),
                   "fails": bool(fails)})
    c3_ok = c3_fail and abs(moment(2, mixed, 1)) == 0 and abs(moment(2, mixed, 3)) == 12

    # C4: M_3 = 0 witness, -e/omega^7 -> 0.
    w5 = [-1 + 0j, 4 + 0j, -5 + 0j, 0j, 5 + 0j, -4 + 0j, 1 + 0j]
    c4 = []
    for w in (mp.mpf("1e-1"), mp.mpf("1e-2"), mp.mpf("1e-3")):
        c4.append({"omega": float(w), "minus_e_over_omega7": float(-mp_energy(3, w5, w) / w ** 7)})
    c4_ok = (abs(moment(3, w5, 1)) == 0 and abs(moment(3, w5, 3)) == 0
             and c4[0]["minus_e_over_omega7"] > c4[1]["minus_e_over_omega7"] > c4[2]["minus_e_over_omega7"] > 0
             and c4[2]["minus_e_over_omega7"] < 1e-6)

    return {
        "prec_bits": ctx.prec,
        "vectors": len(vectors),
        "certified_cases": len(rows),
        "certified_pass": bool(cert_ok),
        "min_ratio": min(r["ratio"] for r in rows),
        "rows": rows,
        "analytic_checks": taylor,
        "small_omega_ratio_K2_generator": sharp,
        "small_omega_ratio_tends_to_16_over_7": bool(sharp_ok),
        "control_C1_stronger_constant": c1,
        "control_C1_fails": bool(c1_fail),
        "control_C2_no_aperture_restriction": c2,
        "control_C2_fails": bool(c2_fail),
        "control_C3_oddness_dropped": c3,
        "control_C3_fails": bool(c3_ok),
        "control_C4_M3_zero": c4,
        "control_C4_no_positive_w7_bound": bool(c4_ok),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output")
    args = ap.parse_args()
    res = check()
    t = res["analytic_checks"]
    ok = (res["certified_pass"] and t["sine_taylor_ok"] and t["remainder_bound_ok"]
          and t["beta_integral_ok"] and t["cauchy_schwarz_and_A_K_ok"]
          and res["small_omega_ratio_tends_to_16_over_7"]
          and res["control_C1_fails"] and res["control_C2_fails"]
          and res["control_C3_fails"] and res["control_C4_no_positive_w7_bound"])
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
