#!/usr/bin/env python3
"""Post-284 independent source falsifier suite (research/regression only).

Every check here is an EXPERIMENTAL or REGRESSION control.  None of it is Lean
theorem authority.  The implementation is deliberately independent of the
repository's R004/R003 numerical helpers: the elementary source matrix and the
canonical equation-(4.4) channels are re-implemented directly from the Lean
definitions

  * ``sourceEntry`` / ``sourceMatrix``      (Zeta23/CCM/SourceMatrix.lean)
  * ``poleComponent`` / ``alphaL`` / ``betaL`` / ``gammaL`` / ``cCorrection`` /
    ``wCorrection`` / ``primeComponent``     (Zeta23/CCM/Components.lean)
  * ``cutoffFreeEntry``                      (Zeta23/CCM/CutoffFreeMatrix.lean)

using mpmath at high precision.  The repository helper
``canonical_source_numeric.py`` is consulted only as a final cross-check.

Checks (handoff v0.4 section 8 ordering):

  F01  M05 candidate regularized whole-energy formula vs canonical matrix,
       channel by channel, with a deliberately wrong normalization as a
       detection-power negative control.
  F02  pole-channel integral identity  int_0^L qBasis * W = poleComponent.
  F03  Fourier convolution representation of S_nm(omega) and of complex e_u.
  F04  exact moment witnesses, K=3 negative source, leading odd endpoint jets.
  F05  moving-vector rational asymptotics (Steps 39-40).
  F06  exact parity-source inertia samples (omega = 0.05, 0.25, 1/3, 0.5, ...)
       and K = 2..9, plus Andreief leading-minor signs of the polynomial
       weight matrix H(a) including the endpoint a = pi.
  F07  rank-two Laplace transform of the source matrix.
  F08  source-only spectral flow on (1/2, 1): zero-level passages (discovery).
  F09  ||Dz||^2 >= 1/(2K+1) under sum z = 0 (sharpness scan).
  F10  toy Schur seam cases LOW / HIGH.
  F11  fourth-moment firewall Q_z(1) = M4(z)/6 and both sign cones with M4 != 0.

Exit code 0 means every assertion held; a failed assertion is a research
finding and stops the suite with a nonzero exit code.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import sympy as sp

DPS = 60
mp.mp.dps = DPS
PI = mp.pi


# ---------------------------------------------------------------------------
# Elementary source matrix, exactly as in SourceMatrix.lean
# ---------------------------------------------------------------------------

def source_entry(omega, n: int, m: int):
    omega = mp.mpf(omega)
    if n == m:
        return 2 * omega * mp.cos(2 * PI * n * omega)
    pot_n = mp.sin(2 * PI * n * omega) / PI
    pot_m = mp.sin(2 * PI * m * omega) / PI
    return (pot_n - pot_m) / (n - m)


def source_matrix(omega, K: int):
    idx = list(range(-K, K + 1))
    return mp.matrix([[source_entry(omega, n, m) for m in idx] for n in idx])


def quad_form(M, u):
    """Repository orientation: sum_ij conj(u_i) M_ij u_j."""
    total = mp.mpc(0)
    n = len(u)
    for i in range(n):
        for j in range(n):
            total += mp.conj(u[i]) * M[i, j] * u[j]
    return total


def energy(omega, K: int, u):
    return mp.re(quad_form(source_matrix(omega, K), [mp.mpc(x) for x in u]))


def centered_moment(u, K: int, r: int):
    return sum(sp.Integer(i - K) ** r * sp.nsimplify(v) for i, v in enumerate(u))


def zero_extend(u, K: int, Kp: int):
    pad = Kp - K
    return [0] * pad + list(u) + [0] * pad


# ---------------------------------------------------------------------------
# Canonical equation-(4.4) channels, exactly as in Components/CutoffFreeMatrix
# ---------------------------------------------------------------------------

def rho(x):
    return mp.exp(x / 2) / (mp.exp(x) - mp.exp(-x))


def W(x):
    return mp.exp(-x / 2) + mp.exp(x / 2)


def von_mangoldt(k: int):
    if k < 2:
        return mp.mpf(0)
    f = sp.factorint(k)
    if len(f) != 1:
        return mp.mpf(0)
    return mp.log(next(iter(f)))


def qbasis(n: int, m: int, y, L):
    """Lean ``qBasis n m y L`` = sourceEntry (1 - y/L) n m (theorem-locked)."""
    return source_entry(1 - mp.mpf(y) / L, n, m)


def _quad(f, a, b):
    return mp.quad(f, [a, (a + b) / 2, b])


def c_correction(L):
    return _quad(lambda x: mp.mpf(1) / 4 if x == 0 else
                 (1 - mp.exp(-x / 2)) / (mp.exp(x) - mp.exp(-x)), 0, L)


def w_correction(L):
    return (mp.euler + mp.log(4 * PI)) / 2 - mp.log((mp.exp(L) + 1) / (mp.exp(L) - 1)) / 2


def alpha_L(n: int, L):
    if n == 0:
        return mp.mpf(0)
    return _quad(lambda x: (PI * n / L) if x == 0 else
                 mp.sin(2 * PI * n * x / L) * rho(x), 0, L) / PI


def beta_L(n: int, L):
    return _quad(lambda x: mp.mpf(1) / 2 if x == 0 else
                 x * mp.cos(2 * PI * n * x / L) * rho(x), 0, L) / L


def gamma_L(n: int, L):
    core = _quad(lambda x: mp.mpf(1) / 4 if x == 0 else
                 (mp.cos(2 * PI * n * x / L) - mp.exp(-x / 2)) * rho(x), 0, L)
    return core + c_correction(L) + w_correction(L)


def pole_component(n: int, m: int, L):
    kappa = 16 * PI ** 2
    C = 32 * L * mp.sinh(L / 4) ** 2
    return C * (L ** 2 - kappa * m * n) / ((L ** 2 + kappa * m ** 2) * (L ** 2 + kappa * n ** 2))


def cutoff_free_arch(n: int, m: int, L):
    if n == m:
        return 2 * (gamma_L(n, L) - c_correction(L)) - 2 * beta_L(n, L)
    return (alpha_L(m, L) - alpha_L(n, L)) / (n - m)


def prime_component(n: int, m: int, L):
    total = mp.mpf(0)
    for k in range(2, int(mp.floor(mp.exp(L))) + 1):
        lam = von_mangoldt(k)
        if lam:
            total += lam / mp.sqrt(k) * qbasis(n, m, mp.log(k), L)
    return total


def channel_matrices(L, K: int):
    idx = list(range(-K, K + 1))
    P = mp.matrix([[pole_component(n, m, L) for m in idx] for n in idx])
    A = mp.matrix([[cutoff_free_arch(n, m, L) for m in idx] for n in idx])
    Q = mp.matrix([[prime_component(n, m, L) for m in idx] for n in idx])
    return P, A, Q


# ---------------------------------------------------------------------------
# F01/F02: M05 candidate regularized whole-energy formula
# ---------------------------------------------------------------------------

def f01_m05_candidate(report):
    out = []
    random.seed(284)
    max_res = mp.mpf(0)
    wrong_min = mp.inf
    cases = [(mp.mpf("0.5"), 2), (mp.mpf("1.2"), 2), (mp.log(2) + mp.mpf("1e-3"), 2),
             (mp.mpf("1.2"), 3), (mp.mpf("2.5"), 3), (mp.mpf("3.3"), 2)]
    for L, K in cases:
        P, A, Q = channel_matrices(L, K)
        for trial in range(2):
            u = [mp.mpc(random.uniform(-1, 1), random.uniform(-1, 1)) for _ in range(2 * K + 1)]
            pole_e = mp.re(quad_form(P, u))
            arch_e = mp.re(quad_form(A, u))
            prime_e = mp.re(quad_form(Q, u))
            canon = pole_e - arch_e - prime_e
            Sfun = lambda om: mp.re(quad_form(source_matrix(om, K), u))
            fL = lambda t: Sfun(1 - t / L)
            c = Sfun(1)
            norm2 = sum(abs(x) ** 2 for x in u)
            assert abs(c - 2 * norm2) < mp.mpf(10) ** (-40), "c_u = e_u(1) = 2||u||^2 failed"
            pole_c = _quad(lambda t: fL(t) * W(t), 0, L)
            arch_c = _quad(lambda t: (fL(t) - c * mp.exp(-t / 2)) * rho(t) if t != 0 else
                           mp.mpf(0), 0, L) + c * w_correction(L)
            prime_c = mp.mpf(0)
            for k in range(2, int(mp.floor(mp.exp(L))) + 1):
                lam = von_mangoldt(k)
                if lam:
                    prime_c += lam / mp.sqrt(k) * fL(mp.log(k))
            cand = pole_c - arch_c - prime_c
            res = abs(canon - cand)
            # Negative control: re-adding the reduced scalar correction
            # canonicalArchScalarCorrection = 2(derived + w) must be detected.
            derived = _quad(lambda x: mp.mpf(1) / 4 if x == 0 else
                            (1 - mp.exp(-x / 2)) * rho(x), 0, L)
            wrong = cand - norm2 * 2 * (derived + w_correction(L))
            wrong_res = abs(canon - wrong)
            max_res = max(max_res, res)
            wrong_min = min(wrong_min, wrong_res)
            out.append({
                "L": mp.nstr(L, 12), "K": K, "trial": trial,
                "canonical_energy": mp.nstr(canon, 20),
                "candidate_energy": mp.nstr(cand, 20),
                "residual": mp.nstr(res, 5),
                "channel_residuals": {
                    "pole": mp.nstr(abs(pole_e - pole_c), 5),
                    "arch": mp.nstr(abs(arch_e - arch_c), 5),
                    "prime": mp.nstr(abs(prime_e - prime_c), 5),
                },
                "double_scalar_negative_control_residual": mp.nstr(wrong_res, 5),
            })
    tol = mp.mpf(10) ** (-25)
    assert max_res < tol, f"M05 candidate mismatch: {max_res}"
    assert wrong_min > mp.mpf(10) ** (-3), "negative control failed to detect double scalar"
    report["F01_M05_candidate_whole_energy"] = {
        "disposition": "NUMERICAL_AGREEMENT_DISCOVERY_NOT_LEAN",
        "max_residual": mp.nstr(max_res, 5),
        "tolerance": mp.nstr(tol, 3),
        "negative_control_min_residual": mp.nstr(wrong_min, 5),
        "cases": out,
        "note": ("Candidate E_u(L) = int f W - int (f - c e^{-t/2}) rho - c wCorrection - "
                 "sum Lambda/sqrt(q) f(log q) agrees with Re u* canonicalSourceMatrix u to "
                 "quadrature precision; re-adding canonicalArchScalarCorrection is detected. "
                 "This is not a Lean proof of M05."),
    }


def f02_pole_identity(report):
    worst = mp.mpf(0)
    for L in (mp.mpf("0.4"), mp.mpf("1.2"), mp.mpf("3.0")):
        for n in range(-3, 4):
            for m in range(-3, 4):
                lhs = _quad(lambda t: qbasis(n, m, t, L) * W(t), 0, L)
                worst = max(worst, abs(lhs - pole_component(n, m, L)))
    assert worst < mp.mpf(10) ** (-30), worst
    report["F02_pole_integral_identity"] = {
        "disposition": "NUMERICAL_AGREEMENT_DISCOVERY_NOT_LEAN",
        "max_residual": mp.nstr(worst, 5),
    }


# ---------------------------------------------------------------------------
# F03: Fourier convolution representation
# ---------------------------------------------------------------------------

def f03_fourier(report):
    worst = mp.mpf(0)
    for omega in (mp.mpf("0.13"), mp.mpf("0.5"), mp.mpf("0.77"), mp.mpf("-0.31"), mp.mpf(1)):
        a = 2 * PI * omega
        for n in range(-3, 4):
            for m in range(-3, 4):
                rep = mp.quad(lambda t: mp.cos(n * t + m * (a - t)), [0, a]) / PI
                worst = max(worst, abs(rep - source_entry(omega, n, m)))
    random.seed(7)
    worst_c = mp.mpf(0)
    for K in (2, 3):
        for omega in (mp.mpf("0.21"), mp.mpf("0.5"), mp.mpf("0.9")):
            u = [mp.mpc(random.uniform(-1, 1), random.uniform(-1, 1)) for _ in range(2 * K + 1)]
            a = 2 * PI * omega
            C = lambda t: sum(u[i] * mp.cos((i - K) * t) for i in range(2 * K + 1))
            T = lambda t: sum(u[i] * mp.sin((i - K) * t) for i in range(2 * K + 1))
            integral = mp.quad(lambda t: mp.conj(C(t)) * C(a - t) - mp.conj(T(t)) * T(a - t), [0, a]) / PI
            direct = quad_form(source_matrix(omega, K), u)
            worst_c = max(worst_c, abs(integral - direct))
    assert worst < mp.mpf(10) ** (-40) and worst_c < mp.mpf(10) ** (-40)
    report["F03_fourier_convolution"] = {
        "disposition": "NUMERICAL_AGREEMENT_DISCOVERY (entrywise case is Lean-compiled separately)",
        "entry_max_residual": mp.nstr(worst, 5),
        "complex_energy_max_residual": mp.nstr(worst_c, 5),
        "note": "integral of conj(C)C(a-t) - conj(T)T(a-t) is real although the integrand need not be",
    }


# ---------------------------------------------------------------------------
# F04: exact moments, negative source, leading endpoint jets
# ---------------------------------------------------------------------------

WITNESSES = {
    ("even", 2): ((1, -4, 6, -4, 1), 4, 24),
    ("odd", 2): ((-1, 2, 0, -2, 1), 3, 12),
    ("even", 3): ((1, -6, 15, -20, 15, -6, 1), 6, 720),
    ("odd", 3): ((-1, 4, -5, 0, 5, -4, 1), 5, 240),
}


def f04_moments_and_jets(report):
    rows = []
    mp.mp.dps = 120
    for (par, K), (u, r, val) in WITNESSES.items():
        assert all(centered_moment(u, K, j) == 0 for j in range(r))
        assert centered_moment(u, K, r) == val
        # leading odd endpoint jet: e_u(w) ~ 2(-(2pi)^2)^r |M_r|^2 w^(2r+1)/(2r+1)!
        coeff = 2 * (-(2 * PI) ** 2) ** r * val ** 2 / mp.factorial(2 * r + 1)
        ratios = []
        for w in (mp.mpf("1e-3"), mp.mpf("1e-4")):
            ratios.append(energy(w, K, u) / (coeff * w ** (2 * r + 1)))
        assert abs(ratios[-1] - 1) < mp.mpf("1e-5"), (par, K, ratios)
        rows.append({"parity": par, "K": K, "u": list(u), "first_moment_order": r,
                     "M_r": val, "jet_order": 2 * r + 1,
                     "leading_sign": "+" if r % 2 == 0 else "-",
                     "ratio_at_1e-4": mp.nstr(ratios[-1], 12)})
    u = (1, -4, 7, -8, 7, -4, 1)
    assert all(centered_moment(u, 3, j) == 0 for j in range(4))
    assert centered_moment(u, 3, 4) == 48
    mp.mp.dps = DPS
    e_half = energy(mp.mpf(1) / 2, 3, u)
    assert abs(e_half + 4) < mp.mpf(10) ** (-40)
    report["F04_moments_negative_source_jets"] = {
        "disposition": "EXACT_REGRESSION (integer moments) + NUMERICAL jet ratios",
        "witnesses": rows,
        "negative_source_K3": {"u": list(u), "M0..M3": 0, "M4": 48,
                               "e_u(1/2)": mp.nstr(e_half, 20),
                               "scope": "elementary sourceMatrix only; not a canonical contact"},
    }


# ---------------------------------------------------------------------------
# F05: moving-vector rational asymptotics
# ---------------------------------------------------------------------------

def _beta(i, j):
    return sp.factorial(i) * sp.factorial(j) / sp.factorial(i + j + 1)


def _conv(poly):
    x = sp.symbols("x")
    terms = sp.Poly(sp.expand(poly), x).terms()
    return sp.nsimplify(sum(ci * cj * _beta(i[0], j[0]) for i, ci in terms for j, cj in terms))


def f05_moving_vectors(report):
    x = sp.symbols("x")
    even_coeff = _conv(-x ** 6 + sp.Rational(3, 11) * x ** 4)
    odd_coeff = -_conv(2 * x ** 5 - sp.Rational(5, 9) * x ** 3)
    assert even_coeff == -sp.Rational(23, 660660)
    assert odd_coeff == sp.Rational(19, 24948)
    # 3/11 and 5/18 are the minimizing / maximizing mixing ratios.
    c = sp.symbols("c")
    I_even = _conv_symbolic(-x ** 6 + c * x ** 4, x)
    I_odd = -_conv_symbolic(2 * x ** 5 - 2 * c * x ** 3, x)
    crit_even = sp.solve(sp.diff(I_even, c), c)
    crit_odd = sp.solve(sp.diff(I_odd, c), c)
    v_e = zero_extend(WITNESSES[("even", 2)][0], 2, 3)
    w_e = WITNESSES[("even", 3)][0]
    v_o = zero_extend(WITNESSES[("odd", 2)][0], 2, 3)
    w_o = WITNESSES[("odd", 3)][0]
    rows = []
    mp.mp.dps = 140  # energies ~ a^13 cancel ~60 digits at omega = 1e-5
    for name, v, w, mix, power, target in (
        ("even", v_e, w_e, mp.mpf(3) / 11, 13, -mp.mpf(23) / (660660 * PI)),
        ("odd", v_o, w_o, mp.mpf(5) / 18, 11, mp.mpf(19) / (24948 * PI)),
    ):
        ratios = []
        for omega in (mp.mpf("1e-3"), mp.mpf("1e-4"), mp.mpf("1e-5")):
            a = 2 * PI * omega
            u = [w[i] + mix * a ** 2 * v[i] for i in range(7)]
            ratios.append(energy(omega, 3, u) / (target * a ** power))
        assert abs(ratios[-1] - 1) < mp.mpf("1e-6"), (name, ratios)
        rows.append({"parity": name, "mix": mp.nstr(mix, 10), "power": power,
                     "target": mp.nstr(target, 15),
                     "ratios": [mp.nstr(r, 12) for r in ratios]})
    mp.mp.dps = DPS
    report["F05_moving_vector_asymptotics"] = {
        "disposition": "EXACT_RATIONAL (beta integrals) + NUMERICAL convergence",
        "even_leading_rational": str(even_coeff),
        "odd_leading_rational": str(odd_coeff),
        "even_mix_critical_point": [str(s) for s in crit_even],
        "odd_mix_critical_point": [str(s) for s in crit_odd],
        "rows": rows,
        "firewall": ("moving vectors have the opposite leading sign to every fixed vector "
                     "of the same parity; fixed-vector leading-sign arguments do not "
                     "generalize to aperture-dependent vectors"),
    }


def _conv_symbolic(poly, x):
    terms = sp.Poly(sp.expand(poly), x).terms()
    return sp.expand(sum(ci * cj * _beta(i[0], j[0]) for i, ci in terms for j, cj in terms))


# ---------------------------------------------------------------------------
# F06: exact source inertia samples and Andreief signs
# ---------------------------------------------------------------------------

def carrier_basis(K: int, parity: str):
    """Exact rational basis of the parity boundary-flat carrier via
    C_u = (1-cos t)^2 x^j (even) or T_u = sin t (1-cos t) x^j (odd)."""
    x = sp.symbols("x")
    vecs = []
    for j in range(K - 1):
        if parity == "even":
            P = sp.Poly(sp.expand((1 - x) ** 2 * x ** j), x)
            # express P in basis [1, 2T_1, ..., 2T_K]; then u_0 = c_0, u_{+-n} = c_n
            coeffs = _chebyshev_coeffs(P, K, "T")
            u = [0] * (2 * K + 1)
            u[K] = coeffs[0]
            for n in range(1, K + 1):
                u[K + n] = coeffs[n] / 2
                u[K - n] = coeffs[n] / 2
        else:
            P = sp.Poly(sp.expand((1 - x) * x ** j), x)
            coeffs = _chebyshev_coeffs(P, K - 1, "U")  # sum_k d_k U_k
            u = [0] * (2 * K + 1)
            for n in range(1, K + 1):
                # T_u/sin t = 2 sum_n u_n U_{n-1}
                u[K + n] = coeffs[n - 1] / 2
                u[K - n] = -coeffs[n - 1] / 2
        vecs.append(u)
    return vecs


def _chebyshev_coeffs(P, deg, kind):
    x = sp.symbols("x")
    basis = [sp.chebyshevt(n, x) if kind == "T" else sp.chebyshevu(n, x) for n in range(deg + 1)]
    cs = sp.symbols(f"c0:{deg + 1}")
    expr = sp.expand(sum(c * b for c, b in zip(cs, basis)) - P.as_expr())
    sol = sp.solve(sp.Poly(expr, x).all_coeffs(), cs, dict=True)[0]
    return [sp.nsimplify(sol.get(c, 0)) for c in cs]


def restricted_gram(omega, K, basis):
    S = source_matrix(omega, K)
    d = len(basis)
    B = [[mp.mpf(sp.Rational(v).p) / sp.Rational(v).q for v in b] for b in basis]
    G = mp.matrix(d, d)
    for a in range(d):
        Sb = [sum(S[i, j] * B[a][j] for j in range(2 * K + 1)) for i in range(2 * K + 1)]
        for b in range(d):
            G[b, a] = sum(B[b][i] * Sb[i] for i in range(2 * K + 1))
    return G


def inertia(G):
    ev = mp.eigsy(G, eigvals_only=True)
    ev = [ev[i] for i in range(G.rows)]
    scale = max(abs(e) for e in ev)
    pos = sum(1 for e in ev if e > 0)
    neg = sum(1 for e in ev if e < 0)
    return pos, neg, min(abs(e) for e in ev) / scale, ev


def f06_inertia_and_andreief(report, kmax: int):
    rows = []
    for K in range(2, kmax + 1):
        for parity in ("even", "odd"):
            basis = carrier_basis(K, parity)
            # carrier membership check (exact)
            for u in basis:
                for r in (0, 1, 2):
                    assert centered_moment(u, K, r) == 0
                if parity == "even":
                    assert all(u[i] == u[2 * K - i] for i in range(2 * K + 1))
                else:
                    assert all(u[i] == -u[2 * K - i] for i in range(2 * K + 1))
            d = K - 1
            expected = ((d + 1) // 2, d // 2) if parity == "even" else (d // 2, (d + 1) // 2)
            for omega in (mp.mpf("0.05"), mp.mpf("0.25"), mp.mpf(1) / 3, mp.mpf("0.45"), mp.mpf("0.5")):
                pos, neg, gap, _ = inertia(restricted_gram(omega, K, basis))
                assert (pos, neg) == expected, (K, parity, omega, pos, neg)
                assert gap > mp.mpf(10) ** (-(DPS - 15)), "near-degenerate: numerically unreliable"
                rows.append({"K": K, "parity": parity, "omega": mp.nstr(omega, 6),
                             "inertia": [pos, neg, 0], "relative_min_abs_eig": mp.nstr(gap, 4)})
    # Andreief signs of H(a) = pi^-1 int_0^a x^j y^k w(t) dt
    minors = []
    for parity in ("even", "odd"):
        for a in (2 * PI * mp.mpf("0.05"), 2 * PI * mp.mpf("0.25"), PI):
            d = 5
            def w(t, a=a):
                xx, yy = mp.cos(t), mp.cos(a - t)
                if parity == "even":
                    return (1 - xx) ** 2 * (1 - yy) ** 2
                return mp.sin(t) * mp.sin(a - t) * (1 - xx) * (1 - yy)
            H = mp.matrix(d, d)
            for j in range(d):
                for k in range(d):
                    H[j, k] = mp.quad(lambda t: mp.cos(t) ** j * mp.cos(a - t) ** k * w(t), [0, a / 2, a]) / PI
            for j in range(d):
                for k in range(d):
                    assert abs(H[j, k] - H[k, j]) <= mp.mpf(10) ** (-40) * (1 + abs(H[j, k]))
            signs = []
            for r in range(1, d + 1):
                D = mp.det(H[0:r, 0:r])
                expect = (-1) ** (r * (r - 1) // 2)
                assert mp.sign(D) == expect, (parity, a, r, D)
                signs.append(int(mp.sign(D)))
            minors.append({"parity_weight": parity, "a": mp.nstr(a, 10), "leading_minor_signs": signs})
    report["F06_exact_source_inertia_samples"] = {
        "disposition": ("NUMERICAL_SAMPLES (omega=1/2 all-K theorem is Lean-compiled separately; "
                        "general omega in (0,1/2) remains an OPEN analytic Andreief lemma)"),
        "rows": rows,
        "andreief_minor_signs": minors,
    }


# ---------------------------------------------------------------------------
# F07: rank-two Laplace transform
# ---------------------------------------------------------------------------

def f07_laplace(report):
    worst = mp.mpf(0)
    for L in (mp.mpf("1.2"), mp.mpf("3.0")):
        K = 3
        a = 4 * PI / L
        idx = range(-K, K + 1)
        for n in idx:
            for m in idx:
                # oscillatory tail: subdivide at quarter-apertures up to 100 L
                pts = [0] + [L * k / 4 for k in range(1, 400)] + [mp.inf]
                lhs = mp.quad(lambda t: mp.exp(-t / 2) * source_entry(t / L, n, m), pts)
                un, um = 1 / (1 + a ** 2 * n ** 2), 1 / (1 + a ** 2 * m ** 2)
                vn, vm = n * un, m * um
                rhs = 8 / L * (un * um - a ** 2 * vn * vm)
                worst = max(worst, abs(lhs - rhs))
    assert worst < mp.mpf(10) ** (-20), worst
    report["F07_rank_two_laplace"] = {
        "disposition": "NUMERICAL_AGREEMENT_DISCOVERY_NOT_LEAN",
        "max_residual": mp.nstr(worst, 5),
        "formula": "int_0^inf e^{-t/2} S_K(t/L) dt = (8/L)(u u^T - a^2 v v^T), a = 4 pi / L",
        "scope": "rank<=2 elementary-source model only; not the canonical energy",
    }


# ---------------------------------------------------------------------------
# F08: source-only spectral flow on (1/2, 1)
# ---------------------------------------------------------------------------

def f08_spectral_flow(report, kmax: int):
    rows = []
    mp.mp.dps = 40
    for K in range(2, min(kmax, 7) + 1):
        for parity in ("even", "odd"):
            basis = carrier_basis(K, parity)
            grid = [mp.mpf(1) / 2 + mp.mpf(k) / 400 for k in range(0, 201)]
            negs = []
            for om in grid:
                _, neg, _, _ = inertia(restricted_gram(om, K, basis))
                negs.append(neg)
            d = K - 1
            expect_neg = d // 2 if parity == "even" else (d + 1) // 2
            assert negs[0] == expect_neg and negs[-1] == 0
            drops = [mp.nstr(grid[i], 6) for i in range(1, len(grid)) if negs[i] != negs[i - 1]]
            rows.append({"K": K, "parity": parity, "neg_at_half": negs[0],
                         "neg_at_one": negs[-1], "grid_change_points": drops,
                         "lower_bound_passages": expect_neg})
    mp.mp.dps = DPS
    report["F08_source_spectral_flow"] = {
        "disposition": "EXPERIMENTAL_SIGNAL (grid of 201 points; passages not certified, not claimed simple or distinct)",
        "rows": rows,
        "firewall": "elementary source-only crossings are not zeta-zero crossings",
    }


# ---------------------------------------------------------------------------
# F09-F11
# ---------------------------------------------------------------------------

def f09_dz_bound(report):
    rows = []
    for K in range(1, 9):
        n = 2 * K + 1
        # minimise sum k^2 |z_k|^2 subject to |z|=1, sum z = 0 : project onto 1^perp
        idx = list(range(-K, K + 1))
        Dm = mp.diag([mp.mpf(k) ** 2 for k in idx])
        P = mp.eye(n) - mp.matrix([[mp.mpf(1) / n] * n for _ in range(n)])
        A = P * Dm * P
        ev = mp.eigsy(A, eigvals_only=True)
        ev = sorted(ev[i] for i in range(n))
        lam = ev[1]  # ev[0] = 0 belongs to the constant direction
        assert lam >= mp.mpf(1) / n - mp.mpf(10) ** (-40)
        rows.append({"K": K, "min_Dz_sq": mp.nstr(lam, 12), "bound_1_over_2K+1": mp.nstr(mp.mpf(1) / n, 12)})
    report["F09_index_action_lower_bound"] = {
        "disposition": "NUMERICAL (bound itself is Lean-compiled separately)", "rows": rows}


def f10_schur_toys(report):
    alpha = mp.mpf("0.7")
    hs = [mp.mpf(10) ** (-k) for k in range(2, 6)]
    low = all((-h ** 3 - alpha * h ** 9) < 0 and (-(-h) ** 3) > 0 for h in hs)
    high = all((h ** 10 - alpha * h ** 9) < 0 and ((-h) ** 10) >= 0 for h in hs)
    assert low and high
    report["F10_schur_toy_cases"] = {"disposition": "REGRESSION", "LOW": low, "HIGH": high}


def f11_fourth_moment_firewall(report):
    x = sp.symbols("x")
    rows = []
    for K in (3, 4, 5):
        basis = carrier_basis(K, "even")
        for j, u in enumerate(basis):
            Q1 = sp.Integer(1)  # Q = x^j has Q(1) = 1
            assert sp.Rational(centered_moment(u, K, 4), 6) == Q1, (K, j)
        pos = zero_extend(WITNESSES[("even", 2)][0], 2, K)
        neg = zero_extend((1, -4, 7, -8, 7, -4, 1), 3, K)
        e_pos = energy(mp.mpf(1) / 2, K, pos)
        e_neg = energy(mp.mpf(1) / 2, K, neg)
        assert e_pos > 0 and e_neg < 0
        rows.append({"K": K, "M4_pos": int(centered_moment(pos, K, 4)), "e_pos": mp.nstr(e_pos, 10),
                     "M4_neg": int(centered_moment(neg, K, 4)), "e_neg": mp.nstr(e_neg, 10)})
    report["F11_fourth_moment_firewall"] = {
        "disposition": "EXACT_REGRESSION (sign cones also Lean-compiled at omega=1/2)",
        "Q_z(1)=M4/6": True, "rows": rows,
        "firewall": "these vectors are not claimed to be canonical contact eigenvectors",
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=None)
    ap.add_argument("--kmax", type=int, default=9)
    ap.add_argument("--quick", action="store_true", help="skip the slow quadrature checks F01/F02/F07")
    args = ap.parse_args()
    report: dict = {
        "suite": "POST284_SOURCE_FALSIFIER_SUITE",
        "authority": "EXPERIMENTAL/REGRESSION ONLY - NOT LEAN THEOREM AUTHORITY",
        "terminal_claim": "RH_OPEN",
        "mpmath_dps": DPS,
    }
    steps = [f03_fourier, f04_moments_and_jets, f05_moving_vectors,
             lambda r: f06_inertia_and_andreief(r, args.kmax),
             lambda r: f08_spectral_flow(r, args.kmax),
             f09_dz_bound, f10_schur_toys, f11_fourth_moment_firewall]
    if not args.quick:
        steps = [f01_m05_candidate, f02_pole_identity, f07_laplace] + steps
    for step in steps:
        step(report)
        print(f"PASS {list(report)[-1]}", flush=True)
    report["overall"] = "ALL_ASSERTIONS_HELD"
    text = json.dumps(report, indent=2, sort_keys=False)
    if args.output:
        args.output.write_text(text + "\n")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
