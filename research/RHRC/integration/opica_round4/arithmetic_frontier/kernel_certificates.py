"""Exact kernel certificates for the missing-arithmetic shape register (increment 6B).

Every quantity here is an integer or a ``Fraction``; no binary floating point is
used. Interval enclosures have dyadic endpoints rounded outward.

Four groups of statements, all about explicit finite objects:

1. The even cutoff-3 pole-neutral boundary-flat vector
   ``v(x) = (-20, 15(1+4x), -6(1+16x), 1+36x)`` with weights ``(1, 2, 2, 2)``:
   its constraints, its norm ``N(x) = 924 + 6048x + 28224x^2``, its non-zero fourth
   moment ``2880x`` (it is not a vector of the quartic moment slice), and the
   closed form ``v0/z + sum 2 v_n z/(z^2+n^2 x) = 2880 x^3 (z^2-1/4)/(z prod (z^2+n^2 x))``.
2. The endpoint polynomial ``q(u) = u^9/9! - u^11/(2*11!) + u^13/(16*13!)``: its
   Laplace transform is ``(s^2-1/4)^2/s^14``, its two weighted moments at ``1/2``
   vanish, and it changes sign exactly twice on ``u > 0`` (in (16.886, 16.887) and (31.029, 31.030)).
3. The fixed cutoff-4 profile ``g(t) = r0 + 2 sum_{k<=4} r_k cos(kt)`` and its
   Volterra square ``q4 = g * g``: the closed form of ``q4``, ``g(0) = 0`` (so
   ``q4(0) = q4'(0) = 0``), the transform ``K = (L g)^2`` with an exact double zero
   at ``s = 1/2``, and the rational constants ``C0, C1, C2`` of the elementary
   bounds ``|q4^(j)(t)| <= C_j (1 + t)``, together with ``C_H = 24 C0 + 4 C1`` and
   ``C_H' = 24 C1 + 4 C2`` as recorded in the 12 November Drive notes.
4. Outward interval enclosures of the integer-drive kernel
   ``J(t) = sum_{n <= e^t} (log n / sqrt n) (q4'(t - log n) + q4(t - log n)/2)``
   at ``t = 4`` and ``t = 6``. The signs differ, so ``J`` is not a nonnegative
   kernel. This implementation is independent of the Drive note's script.

Labels: groups 1-3 are exact algebra (FINITE CERTIFICATE); group 4 is a finite
interval certificate for two values of one explicit function. None of this is an
estimate at late apertures, a bound on any arithmetic pairing, Step 4 or RH,
which remain OPEN.

usage: kernel_certificates.py [--write OUT_JSON]
"""
from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path

SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_KERNEL_CERTIFICATES_V1'
BITS = 256
TAYLOR_TERMS = 110
ATANH_TERMS = 120


class CertificateFailure(ArithmeticError):
    """Raised when an exact or interval check fails."""


def check(value: bool, message: str) -> None:
    if not value:
        raise CertificateFailure(message)


def frac(x: F) -> str:
    return '%d/%d' % (x.numerator, x.denominator) if x.denominator != 1 else str(x.numerator)


# ---------------------------------------------------------------- polynomials
# A polynomial is a dict from exponent tuples to non-zero Fractions.

def padd(*ps: dict) -> dict:
    out: dict = {}
    for p in ps:
        for e, c in p.items():
            out[e] = out.get(e, F(0)) + c
    return {e: c for e, c in out.items() if c != 0}


def pmul(p: dict, q: dict) -> dict:
    out: dict = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(a + b for a, b in zip(e1, e2))
            out[e] = out.get(e, F(0)) + c1 * c2
    return {e: c for e, c in out.items() if c != 0}


def pscale(p: dict, c: F) -> dict:
    return {e: c * v for e, v in p.items() if c * v != 0}


def pprod(ps: list) -> dict:
    out = {tuple(0 for _ in next(iter(ps[0]))): F(1)}
    for p in ps:
        out = pmul(out, p)
    return out


# Variables (x, z) for group 1.
X = {(1, 0): F(1)}
Z = {(0, 1): F(1)}
ONE2 = {(0, 0): F(1)}


def const2(c: F) -> dict:
    return {(0, 0): F(c)} if c != 0 else {}


def cutoff3_algebra() -> dict:
    """Group 1: exact identities of the even cutoff-3 vector."""
    v = [const2(F(-20)),
         pscale(padd(ONE2, pscale(X, F(4))), F(15)),
         pscale(padd(ONE2, pscale(X, F(16))), F(-6)),
         padd(ONE2, pscale(X, F(36)))]
    w = [F(1), F(2), F(2), F(2)]
    moment0 = padd(*[pscale(v[n], w[n]) for n in range(4)])
    moment2 = padd(*[pscale(v[n], w[n] * n * n) for n in range(4)])
    moment4 = padd(*[pscale(v[n], w[n] * n ** 4) for n in range(4)])
    norm = padd(*[pscale(pmul(v[n], v[n]), w[n]) for n in range(4)])
    check(moment0 == {} and moment2 == {}, 'cutoff-3 boundary flatness')
    check(norm == {(0, 0): F(924), (1, 0): F(6048), (2, 0): F(28224)}, 'cutoff-3 norm N(x)')
    check(moment4 == {(1, 0): F(2880)}, 'cutoff-3 fourth moment 2880 x')
    # Pole neutrality: sum w_n v_n / (1/4 + n^2 x) = 0, cleared by prod (1/4 + n^2 x).
    den = [padd(const2(F(1, 4)), pscale(X, F(n * n))) for n in range(4)]
    pole = padd(*[pscale(pmul(v[n], pprod([den[m] for m in range(4) if m != n])), w[n]) for n in range(4)])
    check(pole == {}, 'cutoff-3 pole neutrality')
    # Closed form of the transform, cleared by z * prod_{n=1..3} (z^2 + n^2 x).
    zz = pmul(Z, Z)
    fac = {n: padd(zz, pscale(X, F(n * n))) for n in (1, 2, 3)}
    lhs = padd(pmul(v[0], pprod([fac[1], fac[2], fac[3]])),
               *[pscale(pmul(pmul(v[n], zz), pprod([fac[m] for m in (1, 2, 3) if m != n])), F(2))
                 for n in (1, 2, 3)])
    rhs = pmul(pscale({(3, 0): F(1)}, F(2880)), padd(zz, const2(F(-1, 4))))
    check(padd(lhs, pscale(rhs, F(-1))) == {}, 'cutoff-3 transform closed form')
    return {
        'vector': ['-20', '15(1+4x)', '-6(1+16x)', '1+36x'], 'weights': [1, 2, 2, 2],
        'boundary_flat': True, 'pole_neutral': True,
        'norm': '924 + 6048 x + 28224 x^2',
        'fourth_moment': '2880 x (non-zero for x > 0: the vector is not in the quartic moment slice)',
        'transform': 'v0/z + sum_{n<=3} 2 v_n z/(z^2+n^2 x) = 2880 x^3 (z^2-1/4)/(z prod_{n<=3} (z^2+n^2 x))',
    }


# ----------------------------------------------------------- endpoint kernel q

Q_COEFF = {9: F(1, factorial(9)), 11: F(-1, 2 * factorial(11)), 13: F(1, 16 * factorial(13))}


def q_end(u: F) -> F:
    return sum((c * u ** k for k, c in Q_COEFF.items()), F(0))


def endpoint_kernel() -> dict:
    """Group 2: the endpoint polynomial and its transform."""
    # Laplace transform sum c_k k! s^-(k+1); times s^14 it is sum c_k k! s^(13-k).
    lap = {}
    for k, c in Q_COEFF.items():
        lap[13 - k] = lap.get(13 - k, F(0)) + c * factorial(k)
    target = {4: F(1), 2: F(-1, 2), 0: F(1, 16)}  # (s^2 - 1/4)^2
    check({e: c for e, c in lap.items() if c != 0} == target, 'Laplace transform of q')
    m0 = sum((c * factorial(k) * 2 ** (k + 1) for k, c in Q_COEFF.items()), F(0))
    m1 = sum((c * factorial(k + 1) * 2 ** (k + 2) for k, c in Q_COEFF.items()), F(0))
    check(m0 == 0 and m1 == 0, 'two vanishing moments at 1/2')
    # q(u) = (u^9/9!) p(u^2) with p(v) = 1 - v/220 + v^2/274560; roots v = 624 +- sqrt(114816).
    check(F(factorial(9), 2 * factorial(11)) == F(1, 220) and F(factorial(9), 16 * factorial(13)) == F(1, 274560),
          'reduced quadratic')
    brackets = []
    for lo, hi in ((F(16886, 1000), F(16887, 1000)), (F(31029, 1000), F(31030, 1000))):
        check(q_end(lo) * q_end(hi) < 0, 'sign change bracket')
        brackets.append([frac(lo), frac(hi)])
    disc = 624 * 624 - 274560
    check(disc == 114816 and isqrt(disc) ** 2 != disc, 'irrational roots')
    check(q_end(F(10)) > 0 and q_end(F(20)) < 0 and q_end(F(40)) > 0, 'sign pattern + - +')
    return {
        'q': 'u^9/9! - u^11/(2*11!) + u^13/(16*13!)',
        'laplace_transform': '(s^2 - 1/4)^2 / s^14',
        'vanishing_moments_at_one_half': ['int q(u) e^{-u/2} du = 0', 'int u q(u) e^{-u/2} du = 0'],
        'sign_changes': brackets, 'sign_pattern': '+ on (0,u1), - on (u1,u2), + on (u2,oo)',
        'reduced_quadratic': 'q(u) = (u^9/9!) (1 - u^2/220 + u^4/274560); u^2 = 624 +- sqrt(114816)',
    }


# -------------------------------------------------------- the cutoff-4 profile

R4 = [F(-1, 2304), F(1, 576), F(-17, 5760), F(37, 20160), F(-13, 32256)]
REPORTED = {'C0': F(107498557, 1820786688000), 'C1': F(158107, 1161216000), 'C2': F(7522859, 22759833600),
            'C_H': F(446451559, 227598336000), 'C_H_prime': F(130581211, 28449792000)}


def r4(j: int) -> F:
    return R4[abs(j)]


def kernel4_coefficients() -> tuple[list[F], list[F]]:
    A = [x * x for x in R4]
    b = [-2 * r4(k) * sum((r4(j) / F(k - j) for j in range(-4, 5) if j != k), F(0)) for k in range(5)]
    return A, b


def cutoff4_kernel() -> dict:
    """Group 3: the cutoff-4 profile, its Volterra square and its constants."""
    A, b = kernel4_coefficients()
    check(b[0] == 0, 'b_0 = 0')
    g0 = R4[0] + 2 * sum(R4[1:], F(0))
    check(g0 == 0, 'g(0) = 0, so q4(0) = q4\'(0) = 0')
    # Volterra square in the Laplace domain: L[q4] = (L[g])^2, as polynomials in s
    # after multiplying by s^2 prod_k (s^2 + k^2)^2.
    S = {(1,): F(1)}
    one = {(0,): F(1)}
    sq = pmul(S, S)
    fac = {k: padd(sq, {(0,): F(k * k)}) for k in range(1, 5)}
    allfac = pprod([fac[k] for k in range(1, 5)])
    # s prod (s^2+k^2) * L[g] = r0 prod + sum 2 r_k s^2 prod_{m != k}
    lg = padd(pscale(allfac, R4[0]),
              *[pscale(pmul(sq, pprod([fac[m] for m in range(1, 5) if m != k])), 2 * R4[k]) for k in range(1, 5)])
    lhs = pmul(lg, lg)
    # s^2 prod (s^2+k^2)^2 * L[q4], with L[t] = 1/s^2, L[t cos kt] = (s^2-k^2)/(s^2+k^2)^2, L[sin kt] = k/(s^2+k^2)
    allfac2 = pmul(allfac, allfac)
    terms = [pscale(allfac2, A[0])]
    for k in range(1, 5):
        rest2 = pprod([pmul(fac[m], fac[m]) for m in range(1, 5) if m != k])
        terms.append(pscale(pmul(pmul(sq, padd(sq, {(0,): F(-k * k)})), rest2), 2 * A[k]))
        terms.append(pscale(pmul(pmul(sq, fac[k]), rest2), -2 * b[k] * k))
    rhs = padd(*terms)
    check(padd(lhs, pscale(rhs, F(-1))) == {}, 'q4 is the Volterra square of g')
    # Double zero of K = (L g)^2 at 1/2: L g(1/2) = 0 and (L g)'(1/2) != 0.
    h = F(1, 2)
    lg_half = R4[0] / h + sum((2 * R4[k] * h / (h * h + k * k) for k in range(1, 5)), F(0))
    dlg_half = -R4[0] / (h * h) + sum((2 * R4[k] * (k * k - h * h) / (h * h + k * k) ** 2 for k in range(1, 5)), F(0))
    check(lg_half == 0 and dlg_half == F(512, 204425), 'exact double zero of K at 1/2')
    C0 = abs(A[0]) + 2 * sum((abs(A[k]) + abs(b[k]) for k in range(1, 5)), F(0))
    C1 = abs(A[0]) + 2 * sum((abs(A[k] - k * b[k]) for k in range(1, 5)), F(0)) + \
        2 * sum((k * abs(A[k]) for k in range(1, 5)), F(0))
    C2 = 2 * sum((abs(-2 * k * A[k] + k * k * b[k]) for k in range(1, 5)), F(0)) + \
        2 * sum((k * k * abs(A[k]) for k in range(1, 5)), F(0))
    mine = {'C0': C0, 'C1': C1, 'C2': C2, 'C_H': 24 * C0 + 4 * C1, 'C_H_prime': 24 * C1 + 4 * C2}
    check(mine == REPORTED, 'constants agree with the Drive notes')
    return {
        'profile': 'g(t) = r0 + 2 sum_{k=1..4} r_k cos(k t)', 'r': [frac(x) for x in R4],
        'volterra_square': 'q4(t) = A0 t + 2 sum_{k=1..4} (A_k t cos kt - b_k sin kt), A_k = r_k^2, '
                           'b_k = -2 r_k sum_{j != k, |j| <= 4} r_|j| / (k - j)',
        'A': [frac(x) for x in A], 'b': [frac(x) for x in b],
        'checks': ['q4 = g * g (Laplace domain, exact)', 'b_0 = 0', 'g(0) = 0 so q4(0) = q4\'(0) = 0',
                   'L g(1/2) = 0 and (L g)\'(1/2) = 512/204425: K = (L g)^2 has an exact double zero at 1/2'],
        'constants': {k: frac(v) for k, v in mine.items()},
        'constant_definitions': {
            'C0': '|A0| + 2 sum (|A_k| + |b_k|): |q4(t)| <= C0 (1 + t) for t >= 0 (elementary)',
            'C1': '|A0| + 2 sum |A_k - k b_k| + 2 sum k |A_k|: |q4\'(t)| <= C1 (1 + t)',
            'C2': '2 sum |k^2 b_k - 2 k A_k| + 2 sum k^2 |A_k|: |q4\'\'(t)| <= C2 (1 + t)',
            'C_H': '24 C0 + 4 C1 (the Drive notes\' drive bound |H(t)| <= C_H (1 + t); paper derivation, DERIVED)',
            'C_H_prime': '24 C1 + 4 C2 (the Drive notes\' bound |H\'(t)| <= C_H\' (1 + t); paper derivation, DERIVED)',
        },
        'agrees_with_drive_constants': True,
    }


# ------------------------------------------------------------------ intervals

class Iv:
    """A closed interval with dyadic endpoints, rounded outward to ``BITS`` bits."""
    __slots__ = ('lo', 'hi')

    def __init__(self, lo: F, hi: F | None = None, exact: bool = False):
        hi = lo if hi is None else hi
        if exact:
            self.lo, self.hi = F(lo), F(hi)
        else:
            scale = 1 << BITS
            n_lo = (F(lo) * scale).__floor__()
            n_hi = -((-F(hi) * scale).__floor__())
            self.lo, self.hi = F(n_lo, scale), F(n_hi, scale)
        check(self.lo <= self.hi, 'interval order')

    def __add__(self, o):
        o = o if isinstance(o, Iv) else Iv(F(o), exact=True)
        return Iv(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.hi, -self.lo, exact=True)

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Iv) else Iv(F(o), exact=True)))

    def __rsub__(self, o):
        return Iv(F(o), exact=True) - self

    def __mul__(self, o):
        o = o if isinstance(o, Iv) else Iv(F(o), exact=True)
        ps = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Iv(min(ps), max(ps))

    __rmul__ = __mul__

    def widen(self, r: F):
        return Iv(self.lo - r, self.hi + r)

    def mid(self) -> F:
        return (self.lo + self.hi) / 2

    def rad(self) -> F:
        return (self.hi - self.lo) / 2


def atanh_series(y: F) -> Iv:
    """Enclosure of atanh(y) for exact 0 <= y <= 1/2."""
    check(0 <= y <= F(1, 2), 'atanh range')
    s, p = F(0), y
    for j in range(ATANH_TERMS):
        s += p / (2 * j + 1)
        p *= y * y
    tail = p / ((2 * ATANH_TERMS + 1) * (1 - y * y))
    return Iv(s, s + tail)


_LOG2: dict = {}


def log_int(n: int) -> Iv:
    """Enclosure of log n for an integer n >= 1: n = 2^k m, log m = 2 atanh((m-1)/(m+1))."""
    if BITS not in _LOG2:  # cached per precision, so a change of BITS never reuses a coarser value
        _LOG2[BITS] = atanh_series(F(1, 3)) * 2
    check(n >= 1, 'log domain')
    k = n.bit_length() - 1
    y = F(n - (1 << k), n + (1 << k))
    return _LOG2[BITS] * k + atanh_series(y) * 2


def inv_sqrt_int(n: int) -> Iv:
    s = isqrt(n << (2 * BITS))
    lo, hi = F(1 << BITS, s + 1), F(1 << BITS, s)
    return Iv(lo, hi)


def cos_sin(x: Iv) -> tuple[Iv, Iv]:
    """Enclosures of cos and sin on an interval with |x| <= 8, by Taylor series at the midpoint.

    The terms m^j/j! are computed by the recurrence t_{j+1} = t_j m/(j+1) and each
    is rounded toward zero to the grid 2^-(BITS+64). With delta that grid step, the
    error of every computed term is at most delta * sum_l |m|^l/l! <= delta e^|m|
    <= delta 3^9, so the summed rounding error is at most TAYLOR_TERMS delta 3^9.
    """
    m = x.mid()
    check(abs(m) <= 8, 'trig range')
    scale = 1 << (BITS + 64)
    c, s, term = F(0), F(0), F(1)
    for j in range(TAYLOR_TERMS):
        if j % 4 == 0:
            c += term
        elif j % 4 == 1:
            s += term
        elif j % 4 == 2:
            c -= term
        else:
            s -= term
        term = term * m / (j + 1)
        term = F((term * scale).__floor__(), scale) if term >= 0 else -F((-term * scale).__floor__(), scale)
    rounding = F(TAYLOR_TERMS * 3 ** 9, scale)
    tail = abs(m) ** TAYLOR_TERMS / factorial(TAYLOR_TERMS)  # Lagrange remainder of either series
    check(tail < F(1, 1 << BITS), 'Taylor tail')
    err = rounding + tail + x.rad()  # |cos'|, |sin'| <= 1 on the interval
    return Iv(c).widen(err), Iv(s).widen(err)


def exp_int_bracket(t: int) -> tuple[int, int]:
    """Integers a < e^t < a + 1 from the exponential series with its tail bound."""
    s, term = F(0), F(1)
    N = 4 * t + 60
    for j in range(N):
        s += term
        term = term * t / (j + 1)
    tail = term / (1 - F(t, N + 1))
    a = s.__floor__()
    check(F(a) < s and s + tail < a + 1, 'e^t is not within one integer bracket')
    return a, a + 1


def drive_kernel_interval(t: int) -> dict:
    """Group 4: an outward enclosure of J(t) = H'(t) + H(t)/2 for the cutoff-4 profile."""
    A, b = kernel4_coefficients()
    lo, hi = exp_int_bracket(t)
    total = Iv(F(0), exact=True)
    for n in range(2, lo + 1):
        ln = log_int(n)
        tau = Iv(F(t), exact=True) - ln
        check(tau.lo >= 0, 'n <= e^t')
        c1, s1 = cos_sin(tau)
        cs = [(Iv(F(1), exact=True), Iv(F(0), exact=True)), (c1, s1)]
        for k in range(2, 5):
            ck, sk = cs[-1]
            cs.append((ck * c1 - sk * s1, sk * c1 + ck * s1))
        q = A[0] * tau
        dq = Iv(A[0], exact=True)
        for k in range(1, 5):
            ck, sk = cs[k]
            q = q + 2 * (A[k] * tau * ck - b[k] * sk)
            dq = dq + 2 * ((A[k] - k * b[k]) * ck - k * A[k] * tau * sk)
        total = total + ln * inv_sqrt_int(n) * (dq + q * F(1, 2))
    sign = 'positive' if total.lo > 0 else ('negative' if total.hi < 0 else 'undetermined')
    check(sign != 'undetermined', 'sign of J(%d) not certified' % t)
    return {'t': t, 'floor_exp_t': lo, 'exp_t_bracket': [lo, hi], 'terms': lo - 1, 'bits': BITS,
            'J_lower': frac(total.lo), 'J_upper': frac(total.hi),
            'J_lower_decimal': decimal(total.lo, 28, 'down'), 'J_upper_decimal': decimal(total.hi, 28, 'up'),
            'sign': sign}


def decimal(x: F, digits: int, direction: str) -> str:
    scale = 10 ** digits
    n = (x * scale).__floor__() if direction == 'down' else -((-x * scale).__floor__())
    sign = '-' if n < 0 else ''
    n = abs(n)
    return '%s%d.%0*d' % (sign, n // scale, digits, n % scale)


DRIVE_ENCLOSURES = {4: (F(576882221463915456955, 10 ** 25), F(576882221463915456956, 10 ** 25)),
                    6: (F(-1292800876274351016932, 10 ** 25), F(-1292800876274351016931, 10 ** 25))}


def compute() -> dict:
    j4, j6 = drive_kernel_interval(4), drive_kernel_interval(6)
    agree = {}
    for row in (j4, j6):
        lo, hi = F(row['J_lower']), F(row['J_upper'])
        dlo, dhi = DRIVE_ENCLOSURES[row['t']]
        agree[str(row['t'])] = (lo <= dhi and dlo <= hi)
    check(j4['sign'] == 'positive' and j6['sign'] == 'negative', 'J changes sign between t = 4 and t = 6')
    return {
        'schema': SCHEMA, 'RH': 'OPEN', 'Step4': 'OPEN',
        'authority': 'FINITE_CERTIFICATE_EXACT_RATIONAL_AND_OUTWARD_DYADIC_INTERVALS',
        'tool_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'cutoff3': cutoff3_algebra(), 'endpoint_kernel': endpoint_kernel(), 'cutoff4_kernel': cutoff4_kernel(),
        'integer_drive_kernel': {'J': 'sum_{n <= e^t} (log n / sqrt n) (q4\'(t - log n) + q4(t - log n)/2)',
                                 'values': [j4, j6],
                                 'intersects_drive_note_enclosure': agree,
                                 'consequence': 'J takes both signs, so S = m * J admits no nonnegative-kernel '
                                                'domination; signed information about the Mertens function is required.'},
        'limits': 'Exact algebra of explicit finite objects and two interval values of one explicit function. '
                  'No statement about late apertures, the Mertens function, any arithmetic pairing, Step 4 or RH.',
    }


def main(argv: list[str]) -> int:
    rec = compute()
    text = json.dumps(rec, indent=1, sort_keys=True) + '\n'
    if len(argv) == 3 and argv[1] == '--write':
        Path(argv[2]).write_text(text, encoding='utf-8')
    else:
        sys.stdout.write(text)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
