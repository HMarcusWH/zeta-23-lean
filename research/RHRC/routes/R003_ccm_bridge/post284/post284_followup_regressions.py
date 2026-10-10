#!/usr/bin/env python3
"""POST284 follow-up (Steps 49-107) research regressions.

Exact SymPy regressions and outward-rounded interval enclosures for the
follow-up handoff packages.  Nothing here is theorem authority: interval
results are recorded as INTERVAL_EVIDENCE (mpmath.iv outward rounding plus an
explicit analytic bound on the singular origin cell), not as Lean/Arb
certificates.  RH stays OPEN; no contact or F04 statement is made.

Checks
------
M30  exact 2x2 stationary crossing negative control (SymPy).
M24  matched-update fast falsifier: T+ - T- = d h^9 - c h^10 + O(h^11).
M47  K=2 odd source energy formula vs the elementary source matrix (SymPy).
M41  K=2 prime-free physical test Q_{2,z}(L), z=(1,-4,6,-4,1): interval signs at
     L in {0.1, 0.4, 0.5, 0.6, 2/3}; sign change bracketed in (0.5, 0.6) < log 2.
M43  K=3 z_minus/z_plus at L=2/3: interval signs (finite-dimensional
     indefiniteness of the prime-free second-order form, fixed vectors only).
M42  explicit prime-free radius sanity check (numerical, K=2).
"""
from __future__ import annotations

import argparse
import json
import math
import sys

import sympy as sp
from mpmath import iv, mp

# ---------------------------------------------------------------------------
# M30 / M24 exact symbolic regressions
# ---------------------------------------------------------------------------

def m30_crossing() -> dict:
    h, lam = sp.symbols("h lambda", real=True)
    D = sp.Matrix([[4, 3], [3, 2]])
    g = sp.Matrix([1, 1])
    A = sp.diag(-h**3, 1)
    B = sp.Matrix([[3, -2 * h**3], [-2 * h**3, 4 + h**3]])
    H = sp.Matrix([[12 - 2 * h**3, 6 - 4 * h**3]])
    rank_one = sp.simplify(B * D - D * A - g * H) == sp.zeros(2, 2)
    T = sp.simplify((H * D.inv() * B.inv() * g)[0, 0])
    T_expected = 1 + h**3 / (12 + 3 * h**3 - 4 * h**6)
    T_ok = sp.simplify(T - T_expected) == 0
    det_ok = sp.simplify(1 - T - A.det() / B.det()) == 0
    d1, d2, d3 = (sp.diff(T, h, k).subs(h, 0) for k in (1, 2, 3))
    # shifted secular scalar T(lambda) at h = 0
    T_lam = sp.simplify((H.subs(h, 0) * D.inv() * (B.subs(h, 0) - lam * sp.eye(2)).inv() * g)[0, 0])
    slope0 = sp.simplify(sp.diff(T_lam, lam).subs(lam, 0))
    slope1 = sp.simplify(sp.diff(T_lam, lam).subs(lam, 1))
    checks = {
        "rank_one_identity": bool(rank_one),
        "det_D": int(D.det()),
        "B0_posdef": bool(B.subs(h, 0).is_positive_definite),
        "T_formula": bool(T_ok),
        "one_minus_T_eq_detA_over_detB": bool(det_ok),
        "T0": str(sp.simplify(T.subs(h, 0))),
        "T1": str(d1), "T2": str(d2), "T3": str(d3),
        "lambda_slope_at_0": str(slope0),
        "lambda_slope_at_1": str(slope1),
        "min_eig_A": "-h^3 (diagonal entry) for small h>0",
    }
    ok = (rank_one and checks["det_D"] == -1 and checks["B0_posdef"] and T_ok and det_ok
          and checks["T0"] == "1" and d1 == 0 and d2 == 0 and d3 == sp.Rational(1, 2)
          and slope0 == sp.Rational(1, 12) and slope1 == sp.Rational(-1, 6))
    return {"package": "M30", "disposition": "EXACT_REGRESSION_PASS" if ok else "FAIL",
            "lean_mirror": "Zeta23.CCM.crossing_rankOne / crossing_secular / crossingA_negative",
            "checks": checks,
            "interpretation": "rank-one intertwining plus cubic tangency T-1=O(h^3) coexists with a "
                              "surviving negative even eigenvalue: no universal no-crossing consequence"}


def m24_falsifier() -> dict:
    h, c, d = sp.symbols("h c d", positive=True)
    A_plus, B_plus = -h**3 - d * h**9, 1 + c * h**7
    A_minus, B_minus = -h**3, sp.Integer(1)
    T_plus = 1 - A_plus / B_plus
    T_minus = 1 - A_minus / B_minus
    diff = sp.series(T_plus - T_minus, h, 0, 11).removeO()
    expected = d * h**9 - c * h**10
    ok = sp.simplify(sp.expand(diff) - expected) == 0
    return {"package": "M24", "disposition": "EXACT_REGRESSION_PASS" if ok else "FAIL",
            "series_through_h10": str(sp.expand(diff)),
            "interpretation": "no uncancelled seventh-order secular crossing; leading change is order 9"}

# ---------------------------------------------------------------------------
# Source matrix helpers
# ---------------------------------------------------------------------------

def sym_entry(w, n, m):
    if n == m:
        return 2 * w * sp.cos(2 * sp.pi * n * w)
    return (sp.sin(2 * sp.pi * n * w) - sp.sin(2 * sp.pi * m * w)) / (sp.pi * (n - m))


def m47_formula() -> dict:
    w = sp.symbols("omega", real=True)
    u = {-2: -1, -1: 2, 0: 0, 1: -2, 2: 1}
    e = sum(u[n] * u[m] * sym_entry(w, n, m) for n in u for m in u)
    a = 2 * sp.pi * w
    f = (6 * a * (4 * sp.cos(a) + sp.cos(2 * a)) + 8 * sp.sin(a) - 19 * sp.sin(2 * a)) / (3 * sp.pi)
    ok = sp.simplify(sp.expand_trig(sp.expand(e - f))) == 0
    vals = {str(x): float(e.subs(w, x)) for x in (sp.Rational(1, 2), sp.Rational(3, 4), 1)}
    ok = ok and abs(vals["1/2"] + 6) < 1e-12 and vals["3/4"] < 0 and abs(vals["1"] - 20) < 1e-12
    return {"package": "M47", "disposition": "EXACT_REGRESSION_PASS" if ok else "FAIL",
            "lean_mirror": "Zeta23.CCM.quadraticForm_oddSourceWitnessK2",
            "values": vals}


def iv_entry(w, n, m):
    if n == m:
        return 2 * w * iv.cos(2 * iv.pi * n * w)
    return (iv.sin(2 * iv.pi * n * w) - iv.sin(2 * iv.pi * m * w)) / (iv.pi * (n - m))


def iv_energy(u: dict, w):
    total = iv.mpf(0)
    keys = [k for k, v in u.items() if v != 0]
    for n in keys:
        for m in keys:
            total += u[n] * u[m] * iv_entry(w, n, m)
    return total


def index_action(z: dict) -> dict:
    return {n: n * c for n, c in z.items()}


def l1(u: dict) -> int:
    return sum(abs(v) for v in u.values())

# ---------------------------------------------------------------------------
# Prime-free physical test  Q_{K,z}(L) = int_0^L t^2 (W(t) - rho(t)) e_{Dz}(1 - t/L) dt
# ---------------------------------------------------------------------------

def Q_interval(z: dict, L_lo: str, L_hi: str | None = None, N: int = 6000, eps: str = "1e-4"):
    """Outward-rounded enclosure of Q on (0, L) for L a point (given as a decimal
    string or rational string).  The origin cell [0, eps] is bounded analytically:
    |t^2 (W - rho)| <= 3 t^2 + t e^{t/2}/2 (sinh t >= t, W <= 3 on [0,1]) and
    |e_u(omega)| <= 2 omega (sum |u_n|)^2 <= 2 (sum |u_n|)^2 from |S_nm(omega)| <= 2 omega
    (exact cosine-integral form, Lean `sourceEntry_eq_cos_integral`)."""
    iv.dps = 30
    L = iv.mpf(L_lo) if L_hi is None else iv.mpf([L_lo, L_hi])
    u = index_action(z)
    E = iv.mpf(eps)
    small = 2 * l1(u) ** 2 * (E ** 3 + E ** 2 * iv.exp(E / 2) / 4)
    step = (L - E) / N
    total = iv.mpf(0)
    for j in range(N):
        ta = E + j * step
        tb = E + (j + 1) * step
        t = iv.mpf([ta.a, tb.b])
        W = iv.exp(-t / 2) + iv.exp(t / 2)
        rho = iv.exp(t / 2) / (iv.exp(t) - iv.exp(-t))
        w = 1 - t / L
        total += step * (t ** 2) * (W - rho) * iv_energy(u, w)
    lo = (total.a - small.b).a   # outward: lower endpoint of the lower bound
    hi = (total.b + small.b).b   # outward: upper endpoint of the upper bound
    mp.dps = 30
    lo_m, hi_m = mp.mpf(lo), mp.mpf(hi)
    sign = "+" if lo_m > 0 else ("-" if hi_m < 0 else "?")
    return mp.nstr(lo_m, 20), mp.nstr(hi_m, 20), sign


def Q_float(z: dict, L: float, n: int = 4000) -> float:
    """Plain composite Simpson value (reporting only, not a certificate)."""
    u = index_action(z)
    def e(w):
        s = 0.0
        for a_, ca in u.items():
            for b_, cb in u.items():
                if ca == 0 or cb == 0:
                    continue
                if a_ == b_:
                    s += ca * cb * 2 * w * math.cos(2 * math.pi * a_ * w)
                else:
                    s += ca * cb * (math.sin(2 * math.pi * a_ * w) - math.sin(2 * math.pi * b_ * w)) / (math.pi * (a_ - b_))
        return s
    def f(t):
        if t == 0:
            return 0.0
        W = math.exp(-t / 2) + math.exp(t / 2)
        rho = math.exp(t / 2) / (math.exp(t) - math.exp(-t))
        return t * t * (W - rho) * e(1 - t / L)
    h = L / n
    s = f(0) + f(L)
    for i in range(1, n):
        s += (4 if i % 2 else 2) * f(i * h)
    return s * h / 3


Z_K2 = {-2: 1, -1: -4, 0: 6, 1: -4, 2: 1}
Z_MINUS = {-3: 0, -2: 1, -1: -4, 0: 6, 1: -4, 2: 1, 3: 0}
Z_PLUS = {-3: 1, -2: -5, -1: 11, 0: -14, 1: 11, 2: -5, 3: 1}


def moments(z: dict, kmax: int = 2):
    return [sum((n ** k) * c for n, c in z.items()) for k in range(kmax + 1)]


def m41(N: int) -> dict:
    rows = []
    for L in ("0.1", "0.4", "0.5", "0.6", "2/3"):
        Lstr = L if "/" not in L else None
        if Lstr is None:
            lo, hi, sign = Q_interval(Z_K2, "0.66666666666666666666666666666",
                                      "0.66666666666666666666666666667", N=N)
            Lf = 2 / 3
        else:
            lo, hi, sign = Q_interval(Z_K2, Lstr, N=N)
            Lf = float(Lstr)
        rows.append({"L": L, "enclosure": [lo, hi], "sign": sign, "simpson": Q_float(Z_K2, Lf)})
    signs = {r["L"]: r["sign"] for r in rows}
    bracket = signs.get("0.5") == "+" and signs.get("0.6") == "-"
    log2 = math.log(2)
    disposition = ("INTERVAL_EVIDENCE_SIGN_CHANGE_BEFORE_LOG2" if bracket and 0.6 < log2
                   else "UNRESOLVED")
    return {"package": "M41", "vector_z": [Z_K2[n] for n in sorted(Z_K2)], "moments_M0_M2": moments(Z_K2),
            "rows": rows, "root_bracket": [0.5, 0.6] if bracket else None,
            "disposition": disposition,
            "falsifies": "universal prime-free positivity of Q_{K,z}(L) for every legal z on (0, log 2)",
            "does_not_imply": "anything about actual canonical contact ground states"}


def m43(N: int) -> dict:
    out = {}
    for name, z in (("z_minus", Z_MINUS), ("z_plus", Z_PLUS)):
        lo, hi, sign = Q_interval(z, "0.66666666666666666666666666666",
                                  "0.66666666666666666666666666667", N=N)
        out[name] = {"vector": [z[n] for n in sorted(z)], "moments_M0_M2": moments(z),
                     "enclosure": [lo, hi], "sign": sign,
                     "simpson": Q_float(z, 2 / 3)}
    indefinite = out["z_minus"]["sign"] == "-" and out["z_plus"]["sign"] == "+"
    flat = all(m == 0 for m in out["z_minus"]["moments_M0_M2"] + out["z_plus"]["moments_M0_M2"])
    return {"package": "M43", "L": "2/3", **out,
            "disposition": ("INTERVAL_EVIDENCE_PRIME_FREE_INDEFINITE" if indefinite and flat
                            else "UNRESOLVED"),
            "scope": "two fixed legal even vectors; not canonical eigenvectors; no contact claim"}


def m42_sanity() -> dict:
    K = 2
    radius = 1 / (2 * math.pi ** 2 * (2 * K + 1) * K ** 2)
    L = 0.9 * radius
    q = Q_float(Z_K2, L, n=2000)
    znorm = sum(c * c for c in Z_K2.values())
    lower = L ** 2 * znorm * (1 / (4 * math.pi ** 2) - L * (2 * K + 1) * K ** 2 / 2)
    return {"package": "M42", "K": K, "radius": radius, "L": L, "Q_simpson": q,
            "derived_lower_bound": lower,
            "disposition": "NUMERIC_SANITY_PASS" if q > 0 and q >= lower * 0.999 else "FAIL",
            "status": "DERIVED paper-level bound; not Lean-compiled"}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", default=None)
    ap.add_argument("--n", type=int, default=6000, help="interval subdivisions for Q enclosures")
    args = ap.parse_args()
    report = {"schema": "post284.followup_regressions.v1", "terminal_claim": "RH_OPEN",
              "authority": "research evidence only; numerical/interval results are never theorem authority",
              "results": [m30_crossing(), m24_falsifier(), m47_formula(), m41(args.n), m43(args.n),
                          m42_sanity()]}
    text = json.dumps(report, indent=2)
    if args.output:
        with open(args.output, "w") as fh:
            fh.write(text)
    print(text)
    bad = [r["package"] for r in report["results"] if r["disposition"] in ("FAIL",)]
    if bad:
        print("FAILED:", bad, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
