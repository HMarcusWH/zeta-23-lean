"""Numpy-free native source assembly for the arithmetic-frontier moment slices.

The parity-reduced canonical source at one native state is rebuilt from the
repository's equation-(4.4) primitives in
``research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py``. Only the
assembly is reorganized: the prime and Archimedean entries are formed from
one-index sums, so the matrix costs O(N * prime powers + N^2) ball operations.
Every number is an Arb ball. The slice equations are the Lean carrier's:
even pole-neutral with physical M0 = M2 = M4 = 0, odd pole-neutral with
physical M1 = M3 = M5 = 0.

Shared by the discovery engine ``native_slice.py`` and the floating-point-free
checker ``independent_check.py``; it is therefore a shared trust boundary.
RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import hashlib
import importlib.util
import math
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_mat, ctx, fmpq

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
BACKEND_PATH = REPO / 'research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py'


def sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_backend():
    spec = importlib.util.spec_from_file_location('_frontier_canonical_source_arb', BACKEND_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rational_arb(q: Fraction) -> arb:
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def quartic_cutoff(L: Fraction) -> int:
    """Exact Nat.ceil (L^4) for a rational aperture."""
    p = L ** 4
    return -((-p.numerator) // p.denominator)


def prime_atoms(Q: int) -> list[tuple[int, int]]:
    """All prime powers q <= Q with their prime p; weight is log p / sqrt q."""
    atoms = []
    for q in range(2, Q + 1):
        m, p = q, 2
        while p * p <= m and m % p:
            p += 1
        if p * p > m:
            p = m
        while m % p == 0:
            m //= p
        if m == 1:
            atoms.append((q, p))
    return atoms


class NativeState:
    """One native state: exact aperture, literal quartic cutoff, frozen prime cell."""

    def __init__(self, L: Fraction, K: int | None = None, bits: int = 192):
        if bits < 80:
            raise ValueError('precision below 80 bits cannot certify')
        ctx.prec = bits
        self.bits = bits
        self.backend = load_backend()
        self.Lq = Fraction(L)
        if self.Lq <= 0:
            raise ValueError('aperture must be positive')
        self.K = quartic_cutoff(self.Lq) if K is None else int(K)
        self.L = rational_arb(self.Lq)
        self.Q = int(math.floor(math.exp(float(self.Lq))))
        cell = self.backend.fixed_cell_membership(self.Q, self.L)
        if not cell['certified']:
            raise ArithmeticError('aperture is not certified inside one prime cutoff cell')
        self.atoms = prime_atoms(self.Q)
        pi = arb.pi()
        self.pi = pi
        self.beta = (self.L / (4 * pi)) ** 2
        self._primitives()

    def _primitives(self) -> None:
        b, L, pi, K = self.backend, self.L, self.pi, self.K
        self.alpha = [b.alpha_L(n, L) for n in range(K + 1)]
        self.beta_n = [b.beta_L(n, L) for n in range(K + 1)]
        self.gamma = [b.source_eq44_gamma_L(n, L) for n in range(K + 1)]
        logs = [(arb(q).log(), arb(p).log() / arb(q).sqrt()) for q, p in self.atoms]
        self.s = []
        self.c = []
        for n in range(K + 1):
            ss, cc = arb(0), arb(0)
            for ell, w in logs:
                t = 2 * pi * n * ell / L
                ss += w * t.sin()
                cc += 2 * w * (1 - ell / L) * t.cos()
            self.s.append(ss / pi)
            self.c.append(cc)
        self.d = [L ** 2 + 16 * pi ** 2 * n * n for n in range(K + 1)]
        self.pole_base = 32 * L * (L / 4).sinh() ** 2

    def _A(self, n: int) -> arb:
        return self.alpha[n] if n >= 0 else -self.alpha[-n]

    def _S(self, n: int) -> arb:
        return self.s[n] if n >= 0 else -self.s[-n]

    def channels(self, n: int, m: int) -> tuple[arb, arb, arb]:
        """(pole, arch, prime) with canonical = pole - arch - prime at signed indices."""
        L, pi = self.L, self.pi
        pole = self.pole_base * (L ** 2 - 16 * pi ** 2 * n * m) / (self.d[abs(n)] * self.d[abs(m)])
        if n != m:
            arch = (self._A(m) - self._A(n)) / (n - m)
            prime = (self._S(m) - self._S(n)) / (n - m)
        else:
            arch = 2 * self.gamma[abs(n)] - 2 * self.beta_n[abs(n)]
            prime = self.c[abs(n)]
        return pole, arch, prime

    def entry(self, n: int, m: int) -> arb:
        pole, arch, prime = self.channels(n, m)
        return pole - arch - prime

    def reduced(self, parity: str, with_channels: bool = False):
        """Exact reflection compression: z^T M z = x^T E x on the parity space."""
        K = self.K
        if parity == 'even':
            idx = list(range(0, K + 1))
        elif parity == 'odd':
            idx = list(range(1, K + 1))
        else:
            raise ValueError('parity must be even or odd')
        dim = len(idx)
        mats = [[[arb(0)] * dim for _ in range(dim)] for _ in range(3)]
        sign = 1 if parity == 'even' else -1
        for r, i in enumerate(idx):
            for c in range(r, dim):
                j = idx[c]
                if parity == 'even' and i == 0 and j == 0:
                    vals = self.channels(0, 0)
                elif parity == 'even' and i == 0:
                    vals = tuple(2 * v for v in self.channels(0, j))
                else:
                    a, b = self.channels(i, j), self.channels(i, -j)
                    vals = tuple(2 * (x + sign * y) for x, y in zip(a, b))
                for k in range(3):
                    mats[k][r][c] = mats[k][c][r] = vals[k]
        pole, arch, prime = (arb_mat(m) for m in mats)
        total = pole - arch - prime
        weights = [1 if (parity == 'even' and i == 0) else 2 for i in idx]
        if with_channels:
            return total, weights, {'pole': pole, 'arch': arch, 'prime': prime}
        return total, weights

    def constraints(self, parity: str) -> arb_mat:
        """The four slice equations on reduced coordinates, from the Lean carrier."""
        L, pi = self.L, self.pi
        rows = []
        if parity == 'even':
            idx = range(0, self.K + 1)
            w = [arb(1) if a == 0 else arb(2) for a in idx]
            rows.append([w[a] for a in idx])                                   # M0
            rows.append([w[a] * a * a for a in idx])                           # M2
            rows.append([w[a] * L / (L ** 2 + 16 * pi ** 2 * a * a) for a in idx])  # pole
            rows.append([w[a] * a ** 4 for a in idx])                          # M4 (slice)
        else:
            idx = list(range(1, self.K + 1))
            rows.append([arb(2 * a) for a in idx])                             # M1
            rows.append([2 * 4 * pi * a / (L ** 2 + 16 * pi ** 2 * a * a) for a in idx])  # pole
            rows.append([arb(2 * a ** 3) for a in idx])                        # M3 (slice)
            rows.append([arb(2 * a ** 5) for a in idx])                        # M5 (slice)
        return arb_mat(rows)


