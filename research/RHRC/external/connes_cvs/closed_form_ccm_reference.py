"""Pinned cutoff-free CCM reference used by the R003 normalization audit.

Adapted from Akiva Groskin's MIT-licensed
`papers/2_guinand_weil_dictionary_tail_order/scripts/verify_dictionary_threeroute.py`
at blob 90576ea92835fff2f9dd2e3aa63ad99829bd17e5 in
HMarcusWH/connes-cvs- commit 5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c.

This file is REFERENCE/ORACLE code only.  It is not imported by Lean and has no
claim-promotion authority.  The formulas implement the cutoff-free finite
Connes--van Suijlekom / Connes--Consani--Moscovici Galerkin matrix used in
Groskin's finite Guinand--Weil dictionary.

MIT license: see sibling LICENSE.
"""
from __future__ import annotations

import mpmath as mp


SOURCE_BLOB_SHA = "90576ea92835fff2f9dd2e3aa63ad99829bd17e5"
SOURCE_COMMIT = "5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c"


def prime_powers(c):
    """Return (q, log p) for prime powers q=p^a <= c, as in the source script."""
    c = mp.mpf(c)
    primes: list[int] = []
    x = 2
    while x <= c:
        if all(x % p for p in primes):
            primes.append(x)
        x += 1
    out = []
    for p in primes:
        q = p
        while q <= c:
            out.append((q, mp.log(p)))
            q *= p
    return out


class CutoffFreeCCM:
    """Closed-form cutoff-free finite CCM/CvS matrix at cutoff c and band N."""

    def __init__(self, c, N: int):
        if mp.mpf(c) <= 1:
            raise ValueError("require c > 1")
        if N < 0:
            raise ValueError("require N >= 0")
        self.c = mp.mpf(c)
        self.N = int(N)
        self.L = mp.log(self.c)
        self.z = mp.e ** (-2 * self.L)
        self.PI = mp.pi
        self.PP = prime_powers(self.c)
        self.idx = range(-self.N, self.N + 1)

    def a_n(self, n: int):
        return mp.mpf(1) / 4 + self.PI * 1j * n / self.L

    def F(self, n: int):
        a = self.a_n(n)
        return mp.hyp2f1(1, a, a + 1, self.z)

    def alpha_L(self, n: int):
        a = self.a_n(n)
        L, PI = self.L, self.PI
        return (
            mp.e ** (-L / 2) * mp.im((2 * L / (L + 4 * PI * 1j * n)) * self.F(n))
            + mp.mpf(1) / 2 * mp.im(mp.digamma(a))
        ) / PI

    def beta_L(self, n: int):
        a = self.a_n(n)
        L, PI = self.L, self.PI
        t1 = -L * mp.e ** (-L / 2) * mp.im((2 * L / (4 * PI * n - 1j * L)) * self.F(n))
        t2 = -(mp.e ** (-L / 2) / 4) * mp.re(mp.lerchphi(self.z, 2, a))
        t3 = mp.mpf(1) / 4 * mp.re(mp.polygamma(1, a))
        return (t1 + t2 + t3) / L

    def c_w(self):
        L, PI = self.L, self.PI
        return (
            mp.mpf(1) / 2 * mp.log((mp.e ** (L / 2) - 1) / (mp.e ** (L / 2) + 1))
            + mp.atan(mp.e ** (L / 2))
            - PI / 4
            + mp.euler / 2
            + mp.mpf(1) / 2 * mp.log(8 * PI)
        )

    def gamma_L(self, n: int):
        a = self.a_n(n)
        L = self.L
        return (
            -mp.e ** (-L / 2) * mp.re((2 * L / (L + 4 * self.PI * 1j * n)) * self.F(n))
            + 2 * mp.e ** (-L / 2) * mp.hyp2f1(mp.mpf(1) / 4, 1, mp.mpf(5) / 4, self.z)
            - mp.mpf(1) / 2 * (mp.re(mp.digamma(a)) - mp.digamma(mp.mpf(1) / 4))
            + self.c_w()
        )

    def prime_source(self, m: int):
        L, PI = self.L, self.PI
        return -(1 / PI) * mp.fsum(
            lp / mp.sqrt(q) * mp.sin(2 * PI * m * (1 - mp.log(q) / L))
            for q, lp in self.PP
        )

    def prime_source_derivative(self, m: int):
        L, PI = self.L, self.PI
        return -2 * mp.fsum(
            lp / mp.sqrt(q) * (1 - mp.log(q) / L)
            * mp.cos(2 * PI * m * (1 - mp.log(q) / L))
            for q, lp in self.PP
        )

    def C(self, m: int):
        L, PI = self.L, self.PI
        return mp.sinh(L / 4) / mp.sqrt(L) / (mp.mpf(1) / 4 + (2 * PI * m / L) ** 2)

    def S(self, m: int):
        L, PI = self.L, self.PI
        return (
            4 * PI * mp.sinh(L / 4) / (L * mp.sqrt(L)) * m
            / (mp.mpf(1) / 4 + (2 * PI * m / L) ** 2)
        )

    def pole_entry(self, m: int, n: int):
        return 2 * (self.C(m) * self.C(n) - self.S(m) * self.S(n))

    def entry(self, m: int, n: int):
        """Full centered-frequency cutoff-free Q_infty entry."""
        pole = self.pole_entry(m, n)
        if m == n:
            p0d = -2 * (self.gamma_L(n) - self.beta_L(n)) + self.prime_source_derivative(n)
            return p0d + pole
        p0m = self.alpha_L(m) + self.prime_source(m)
        p0n = self.alpha_L(n) + self.prime_source(n)
        return (p0m - p0n) / (m - n) + pole

    def build_full(self):
        """Return Q_infty on indices -N,...,N."""
        dim = 2 * self.N + 1
        Q = mp.matrix(dim, dim)
        idx = list(self.idx)
        for i, m in enumerate(idx):
            for j, n in enumerate(idx):
                Q[i, j] = self.entry(m, n)
        return Q

    def build_even(self):
        """Return the reversal-even block, matching source `build_Me`."""
        N = self.N
        Me = mp.matrix(N + 1, N + 1)
        for i in range(N + 1):
            for j in range(N + 1):
                if i == 0 and j == 0:
                    Me[i, j] = self.entry(0, 0)
                elif i == 0:
                    Me[i, j] = (self.entry(0, j) + self.entry(0, -j)) / mp.sqrt(2)
                elif j == 0:
                    Me[i, j] = (self.entry(i, 0) + self.entry(-i, 0)) / mp.sqrt(2)
                else:
                    Me[i, j] = self.entry(i, j) + self.entry(i, -j)
        return Me
