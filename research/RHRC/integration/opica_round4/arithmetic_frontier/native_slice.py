"""Independent native moment-slice replay with rigorous Arb enclosures.

The parity-reduced canonical source at one native state is reconstructed from
the repository's direct equation-(4.4) primitives in
``research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py``. Only the
assembly is reorganized: the prime and Archimedean entries are formed from
one-index sums, so the matrix costs O(N * prime powers + N^2) ball operations.
Every number is an Arb ball; floating values only propose coordinates.

The carriers are exactly the Lean moment slices of
``Zeta23.OPICARound4.ArithmeticFrontier``: the even slice is the even
pole-neutral carrier with physical M4 = 0, the odd slice has M3 = M5 = 0. A
floating W-orthonormal basis is proposed and then corrected in Arb on four
pivot coordinates, so every basis column lies exactly in the slice.

Acceptance is research certification of a finite inequality, never a Lean
proof. A favorable floating eigenvalue is a diagnostic only. RH and Step 4
remain OPEN.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from flint import arb, arb_mat, ctx, fmpq

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
BACKEND_PATH = REPO / 'research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py'
CAPS = {'RH': 'OPEN', 'Step4': 'OPEN', 'authority': 'RESEARCH_CERTIFICATION_NOT_LEAN_AUTHORITY'}
DISPOSITIONS = ('CERTIFIED', 'FALSIFIED_BOUND', 'UNKNOWN_PRECISION', 'RESOURCE_STOP', 'NOT_ELIGIBLE')


def sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def array_sha256(a: np.ndarray) -> str:
    """Hash of the exact float64 proposal bytes (C order, little endian)."""
    return hashlib.sha256(np.ascontiguousarray(a, dtype='<f8').tobytes()).hexdigest()


def load_backend():
    spec = importlib.util.spec_from_file_location('_frontier_canonical_source_arb', BACKEND_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rational_arb(q: Fraction) -> arb:
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


def to_float(m: arb_mat) -> np.ndarray:
    return np.array([[float(x.mid()) for x in row] for row in m.tolist()], dtype=float)


def from_float(a: np.ndarray) -> arb_mat:
    return arb_mat([[arb(float(x)) for x in row] for row in np.atleast_2d(a)])


def pivots_for(C: np.ndarray, allowed: int) -> list[int]:
    """Column-pivoted Gram-Schmidt on row-scaled constraints within a prefix."""
    A = C[:, :allowed] / np.linalg.norm(C[:, :allowed], axis=1, keepdims=True)
    chosen, basis = [], []
    for _ in range(A.shape[0]):
        R = A.copy()
        for q in basis:
            R -= np.outer(q, q @ R)
        norms = np.linalg.norm(R, axis=0)
        norms[chosen] = -1
        j = int(np.argmax(norms))
        chosen.append(j)
        basis.append(R[:, j] / norms[j])
    return chosen


def kernel_basis(C: np.ndarray, weights: list[int], prefix: int) -> np.ndarray:
    """Floating W-orthonormal basis of the constraint kernel on indices < prefix."""
    dim = C.shape[1]
    w = np.sqrt(np.array(weights[:prefix], dtype=float))
    Cs = C[:, :prefix] / np.linalg.norm(C[:, :prefix], axis=1, keepdims=True) / w
    q, _ = np.linalg.qr(Cs.T, mode='complete')
    Z = np.zeros((dim, prefix - C.shape[0]))
    Z[:prefix] = q[:, C.shape[0]:] / w[:, None]
    return Z


def flag_basis(C: np.ndarray, weights: list[int], split: int | None) -> tuple[np.ndarray, int]:
    """W-orthonormal flag: carrier on indices < split, then its W-complement."""
    dim = C.shape[1]
    full = kernel_basis(C, weights, dim)
    if split is None:
        return full, 0
    low = kernel_basis(C, weights, split)
    W = np.array(weights, dtype=float)
    rest = full - low @ (low.T @ (W[:, None] * full))
    u, sv, _ = np.linalg.svd(np.sqrt(W)[:, None] * rest, full_matrices=False)
    k = full.shape[1] - low.shape[1]
    high = u[:, :k] / np.sqrt(W)[:, None]
    return np.hstack([low, high]), low.shape[1]


def exact_basis(Z: np.ndarray, C: arb_mat, prefix_for_column: list[int]) -> arb_mat:
    """Correct each floating column on four pivots so C y = 0 holds exactly."""
    Cf = to_float(C)
    groups: dict[int, list[int]] = {}
    for j, p in enumerate(prefix_for_column):
        groups.setdefault(p, []).append(j)
    Y = from_float(Z)
    rows = Y.tolist()
    for prefix, cols in groups.items():
        piv = pivots_for(Cf, prefix)
        Cp = arb_mat([[C[r, p] for p in piv] for r in range(C.nrows())])
        Zc = from_float(Z[:, cols])
        delta = Cp.solve(C * Zc)
        for k, j in enumerate(cols):
            for r, p in enumerate(piv):
                rows[p][j] = rows[p][j] - delta[r, k]
    Y = arb_mat(rows)
    residual = C * Y
    if not all(residual[i, j].contains(0) for i in range(residual.nrows()) for j in range(residual.ncols())):
        raise ArithmeticError('exact slice correction failed')
    return Y


def weighted(Y: arb_mat, weights: list[int]) -> arb_mat:
    return arb_mat([[weights[i] * Y[i, j] for j in range(Y.ncols())] for i in range(Y.nrows())])


def identity(n: int, scale: arb | int = 1) -> arb_mat:
    return arb_mat([[arb(scale) if i == j else arb(0) for j in range(n)] for i in range(n)])


def frobenius_sq(E: arb_mat) -> arb:
    """A ball containing ||E_true||_F^2 for every matrix inside the ball matrix."""
    total = arb(0)
    for row in E.tolist():
        for x in row:
            total += x * x
    return total


def upper(x: arb) -> float:
    """A float that is >= every point of the ball (outward rounded)."""
    return math.nextafter(float(x.mid()) + float(x.rad()), math.inf) + 2.0 ** -1000


def lower(x: arb) -> float:
    return math.nextafter(float(x.mid()) - float(x.rad()), -math.inf) - 2.0 ** -1000


def certify_psd(A: arb_mat, tau: Fraction | float) -> dict:
    """Shifted Cholesky certificate for a symmetric ball matrix.

    For R exact, E = A - tau I - R R^T is symmetric and enclosed in Arb. If
    ||E||_F < tau then A >= (tau - ||E||_F) I > 0, because R R^T >= 0 and the
    spectral norm is at most the Frobenius norm.
    """
    n = A.nrows()
    tau = Fraction(tau).limit_denominator(1 << 60) if not isinstance(tau, Fraction) else tau
    Af = to_float(A)
    Af = (Af + Af.T) / 2
    try:
        R = np.linalg.cholesky(Af - float(tau) * np.eye(n))
    except np.linalg.LinAlgError:
        return {'status': 'UNKNOWN_PRECISION', 'reason': 'floating shifted factorization failed',
                'tau': str(tau)}
    Ra = from_float(R)
    t = rational_arb(tau)
    E = A - Ra * Ra.transpose() - identity(n, t)
    fro2 = frobenius_sq(E)
    ok = bool(fro2 < t * t)
    fro_up = upper(fro2.sqrt()) if fro2 > 0 else upper(fro2)
    return {'status': 'CERTIFIED' if ok else 'UNKNOWN_PRECISION', 'tau': str(tau),
            'residual_frobenius_upper': fro_up,
            'certified_lower_eigenvalue': lower(t - fro2.sqrt()) if ok else None}


def certify_ldl(A: arb_mat) -> dict:
    """Interval LDL^T: every pivot certified positive implies A > 0."""
    n = A.nrows()
    M = [row[:] for row in A.tolist()]
    pivots = []
    for k in range(n):
        p = M[k][k]
        if not (p > 0):
            return {'status': 'UNKNOWN_PRECISION', 'failed_pivot': k, 'pivot': p.str(10)}
        pivots.append(p)
        for i in range(k + 1, n):
            f = M[i][k] / p
            for j in range(k + 1, i + 1):
                M[i][j] = M[i][j] - f * M[j][k]
    smallest = min(pivots, key=lambda x: float(x.mid()))
    return {'status': 'CERTIFIED', 'pivots': n, 'smallest_pivot_lower': lower(smallest)}


def mid_matrix(M: arb_mat) -> arb_mat:
    return arb_mat([[x.mid() for x in row] for row in M.tolist()])


def mid_cholesky(A: arb_mat) -> list[list[arb]] | None:
    """Plain Cholesky of the midpoint matrix at the working precision.

    Only the midpoints of the result are used: the factor is an exact proposal
    and its error is paid by the enclosed residual of ``certify_shifted``.
    """
    n = A.nrows()
    M = [[x.mid() for x in row] for row in A.tolist()]
    R = [[arb(0)] * n for _ in range(n)]
    for j in range(n):
        s = M[j][j]
        for k in range(j):
            s -= R[j][k] * R[j][k]
        s = s.mid()
        if not (s > 0):
            return None
        d = s.sqrt().mid()
        R[j][j] = d
        for i in range(j + 1, n):
            t = M[i][j]
            for k in range(j):
                t -= R[i][k] * R[j][k]
            R[i][j] = (t / d).mid()
    return R


def certify_shifted(A: arb_mat, tau: Fraction) -> dict:
    """High-precision form of ``certify_psd``: the factor comes from Arb midpoints."""
    n = A.nrows()
    t = rational_arb(tau)
    R = mid_cholesky(A - identity(n, t))
    if R is None:
        return {'status': 'UNKNOWN_PRECISION', 'reason': 'midpoint shifted factorization failed', 'tau': str(tau)}
    Ra = arb_mat(R)
    E = A - Ra * Ra.transpose() - identity(n, t)
    fro2 = frobenius_sq(E)
    ok = bool(fro2 < t * t)
    return {'status': 'CERTIFIED' if ok else 'UNKNOWN_PRECISION', 'tau': str(tau),
            'residual_frobenius_sq_ball': fro2.str(6)}


def bottom_bracket(F: arb_mat, G: arb_mat, x0: np.ndarray, iterations: int = 4) -> dict:
    """Rigorous two-sided bracket of min_x x^T F x / x^T G x on the slice.

    Upper: the Rayleigh quotient of an exact vector from inverse iteration.
    Lower: a margin m with F - m G >= 0, certified by a shifted factorization.
    """
    Fm, Gm = mid_matrix(F), mid_matrix(G)
    x = from_float(x0.reshape(-1, 1))
    for _ in range(iterations):
        y = Fm.solve(Gm * x, algorithm='approx')
        scale = (y.transpose() * y)[0, 0].mid().sqrt().mid()
        x = arb_mat([[(y[i, 0] / scale).mid()] for i in range(y.nrows())])
    num = (x.transpose() * F * x)[0, 0]
    den = (x.transpose() * G * x)[0, 0]
    rho = num / den
    out = {'_rho': rho, 'rayleigh_upper': rho.str(8), 'rayleigh_upper_log10': float(rho.mid().log() / arb(10).log()) if rho > 0 else None}
    if not (rho > 0):
        out['status'] = 'NEGATIVE_OR_UNRESOLVED_UPPER'
        out['rigorous_negative'] = bool(rho < 0)
        return out
    m_arb = rho.mid() / 4
    e = int(math.floor(float(m_arb.log() / arb(2).log())))
    margin = Fraction(1, 1 << -e) if e < 0 else Fraction(1 << e)
    n = F.nrows()
    cert = certify_shifted(F - rational_arb(margin) * G, margin)
    out.update({'margin_lower': '2^%d' % e if e < 0 else str(margin), 'margin_certificate': cert,
                'status': 'BRACKETED' if cert['status'] == 'CERTIFIED' else 'UPPER_ONLY',
                'statement': 'm ||x||^2 <= Q_p(L,x) for all x in the slice, and the exact vector attains <= rho ||x||^2'})
    return out


def rigorous_form(M: arb_mat, v: np.ndarray) -> arb:
    x = from_float(v.reshape(-1, 1))
    return (x.transpose() * M * x)[0, 0]


def certify_margin(F: arb_mat, G: arb_mat, m: Fraction, rho: arb, ldl: bool = False) -> dict:
    """Certify Q_p >= m ||x||^2 on the slice, or refute it with the exact vector."""
    rec = {'margin': str(m), 'statement': 'Q_p(L,x) >= %s ||x||^2 for every x in the slice' % m}
    if rho < rational_arb(m):
        return {**rec, 'status': 'FALSIFIED_BOUND', 'reason': 'exact slice vector has Rayleigh value below the margin'}
    gap = (rho - rational_arb(m)).mid()
    if not (gap > 0):
        return {**rec, 'status': 'UNKNOWN_PRECISION', 'reason': 'margin not separated from the Rayleigh value'}
    e = int(math.floor(float((gap / 4).log() / arb(2).log())))
    tau = Fraction(1, 1 << -e) if e < 0 else Fraction(1 << e)
    cert = certify_shifted(F - rational_arb(m) * G, tau)
    if ldl and cert['status'] != 'CERTIFIED':
        cert = {**certify_ldl(F - rational_arb(m) * G), 'method': 'INTERVAL_LDL'}
    return {**rec, **cert}


def slice_run(L: Fraction, parity: str, eps_list: list[Fraction] = (), split: int | None = None,
              bits: int = 192, ldl: bool = False, margins: list[Fraction] | None = None,
              K: int | None = None, bracket: bool = False) -> dict:
    t0 = time.time()
    st = NativeState(L, K=K, bits=bits)
    M, weights, chans = st.reduced(parity, with_channels=True)
    C = st.constraints(parity)
    Cf = to_float(C)
    dim_expected = st.K - 3 if parity == 'even' else st.K - 4
    split_idx = None
    if split is not None:
        split_idx = split + 1 if parity == 'even' else split
    Z, nlow = flag_basis(Cf, weights, split_idx)
    if Z.shape[1] != dim_expected:
        raise ArithmeticError('proposed basis dimension differs from the proved slice dimension')
    prefixes = [split_idx] * nlow + [len(weights)] * (Z.shape[1] - nlow)
    Y = exact_basis(Z, C, prefixes)
    WY = weighted(Y, weights)
    F = Y.transpose() * M * Y
    G = Y.transpose() * WY
    t_build = time.time() - t0
    gram = certify_psd(G, Fraction(1, 4))
    if gram['status'] != 'CERTIFIED':
        raise ArithmeticError('basis Gram not certified positive; rank not established')
    Ff, Gf = to_float(F), to_float(G)
    Ff, Gf = (Ff + Ff.T) / 2, (Gf + Gf.T) / 2
    Lg = np.linalg.cholesky(Gf)
    Li = np.linalg.inv(Lg)
    evals, evecs = np.linalg.eigh(Li @ Ff @ Li.T)
    vb = Li.T @ evecs[:, 0]
    energy_v = rigorous_form(F, vb)
    norm_v = rigorous_form(G, vb)
    x = from_float(vb.reshape(-1, 1))
    xs = Y * x
    budget = {k: (xs.transpose() * chans[k] * xs)[0, 0] for k in ('pole', 'arch', 'prime')}
    rayleigh_upper = energy_v / norm_v
    channel_floor = {}
    for name, sign in (('pole', 1), ('minus_arch', -1), ('minus_prime', -1)):
        key = 'pole' if name == 'pole' else name.split('_')[1]
        Pf = sign * to_float(Y.transpose() * chans[key] * Y)
        ev, vec = np.linalg.eigh(Li @ ((Pf + Pf.T) / 2) @ Li.T)
        w = Li.T @ vec[:, 0]
        cm = sign * (from_float(w.reshape(-1, 1)).transpose() * (Y.transpose() * chans[key] * Y) * from_float(w.reshape(-1, 1)))[0, 0]
        channel_floor[name] = {'floating_min': float(ev[0]), 'floating_max': float(ev[-1]),
                               'rigorous_rayleigh_at_min_vector': (cm / rigorous_form(G, w)).str(10)}
    hashes = {'gram_sha256': array_sha256(Gf),
              'prime_power_list_sha256': hashlib.sha256(json.dumps([q for q, _ in st.atoms]).encode()).hexdigest(),
              'basis_proposal_sha256': array_sha256(Z)}
    record = {
        'schema': 'OPICA4_ARITHMETIC_FRONTIER_NATIVE_SLICE_RUN_V1', **CAPS, 'hashes': hashes,
        'state': {'L_exact': str(st.Lq), 'cutoff_expression': 'originalDetectorQuarticCutoff(L)=ceil(L^4)' if K is None else 'EXPLICIT_K',
                  'K': st.K, 'Q': st.Q, 'prime_powers': [q for q, _ in st.atoms], 'parity': parity,
                  'carrier': 'evenMomentSlice' if parity == 'even' else 'oddMomentSlice',
                  'dimension': Z.shape[1], 'metric': 'PHYSICAL_INHERITED_EUCLIDEAN',
                  'state_kind': 'ACTUAL_STATE'},
        'precision_bits': bits,
        'source': {'backend': str(BACKEND_PATH.relative_to(REPO)), 'backend_sha256': sha256(BACKEND_PATH),
                   'replay_module_sha256': sha256(Path(__file__))},
        'basis': {'kind': 'FLOAT_W_ORTHONORMAL_PROPOSAL_EXACTLY_CORRECTED_ON_FOUR_PIVOTS',
                  'gram_certificate': gram, 'flag_split_index': split, 'low_dimension': nlow},
        'endpoint_certificates': [],
        'diagnostics': {
            'floating_generalized_eigenvalues_lowest': [float(e) for e in evals[:6]],
            'floating_generalized_eigenvalue_highest': float(evals[-1]),
            'near_null_count_below_1e-8': int(np.sum(np.abs(evals) < 1e-8)),
            'authority': 'EXPERIMENTAL_SIGNAL_FLOATING_ONLY'},
        'channel_extremes_on_slice': {**channel_floor,
            'meaning': 'each channel alone on the same slice and metric; the native form is pole - arch - prime',
            'authority': 'FLOATING_SPECTRA_WITH_ONE_RIGOROUS_RAYLEIGH_VALUE_PER_CHANNEL'},
        'bottom_vector_budget': {
            'rayleigh_upper_bound': rayleigh_upper.str(12),
            'pole': budget['pole'].str(12), 'arch': budget['arch'].str(12), 'prime': budget['prime'].str(12),
            'energy': energy_v.str(12), 'physical_norm_sq': norm_v.str(12),
            'relation': 'energy = pole - arch - prime on this exact slice vector; the Rayleigh value bounds the slice bottom from above',
            'authority': 'RIGOROUS_ENCLOSURES_FOR_ONE_EXACT_SLICE_VECTOR'},
    }
    if bracket:
        record['bottom_bracket'] = bottom_bracket(F, G, vb)
    for eps in eps_list:
        e = rational_arb(Fraction(eps))
        B = F + e * G
        cert = certify_psd(B, Fraction(eps) / 2)
        if ldl and cert['status'] != 'CERTIFIED':
            cert = {**certify_ldl(B), 'method': 'INTERVAL_LDL'}
        cert['tolerance'] = str(Fraction(eps))
        cert['statement'] = 'Q_p(L,x) >= -%s ||x||^2 for every x in the slice' % Fraction(eps)
        record['endpoint_certificates'].append(cert)
    if margins:
        rho = record.get('bottom_bracket', {}).get('_rho') or (energy_v / norm_v)
        for mg in margins:
            record['endpoint_certificates'].append(certify_margin(F, G, Fraction(mg), rho, ldl))
    if split is not None:
        record['block_tests'] = [block_test(F, G, nlow, Fraction(eps)) for eps in eps_list]
    if 'bottom_bracket' in record:
        record['bottom_bracket'].pop('_rho', None)
    record['budget_records'] = budget_records(record)
    record['seconds'] = round(time.time() - t0, 1)
    record['build_seconds'] = round(t_build, 1)
    return record


def sub(M: arb_mat, rows: range, cols: range) -> arb_mat:
    return arb_mat([[M[i, j] for j in cols] for i in rows])


def rational_below(x: float, digits: int = 1000) -> Fraction:
    return Fraction(math.floor(x * digits), digits)


def rational_above(x: float, digits: int = 1000) -> Fraction:
    return Fraction(math.ceil(x * digits), digits)


def block_test(F: arb_mat, G: arb_mat, k: int, eps: Fraction, degree: int = 64,
               reported: tuple[Fraction, Fraction] | None = (Fraction(49, 100), Fraction(9)),
               reported_label: str = 'REPORTED_L4_HALF_CONSTANTS') -> dict:
    """Block surrogates on the Fourier-prefix flag of the shifted pencil B = F + eps G.

    D is the low block (slice through the split), A the W-orthogonal complement
    block and C the complete mixed coupling. Three statements are tested:

    * the scalar inverse-gap surrogate D - a^{-1} C C^T >= 0 (the X = 0 case of
      the Lean inverse-residual certificate), refuted for every admissible
      a <= lambda_min(A) by one rigorous witness at a Rayleigh upper bound rho;
    * the coupling-preserving polynomial certificate X = P_m(A) C^T with
      P_m(A) = b^{-1} sum_{j<m} (I - A/b)^j, checked in the exact form of
      ``blockEnergy_nonneg_of_inverse_residual_certificate``;
    * the direct shifted Cholesky certificate of B itself (the native form).
    """
    B = F + rational_arb(eps) * G
    n = B.nrows()
    lo, hi = range(k), range(k, n)
    D, C, A = sub(B, lo, lo), sub(B, lo, hi), sub(B, hi, hi)
    Af, Cf = to_float(A), to_float(C)
    Af = (Af + Af.T) / 2
    ea, va = np.linalg.eigh(Af)
    out = {'target_tolerance': str(eps), 'low_dimension': k, 'high_dimension': n - k,
           'coordinates': 'FOURIER_PREFIX_FLAG_W_ORTHONORMAL_PROPOSAL',
           'high_block_floating_extremes': [float(ea[0]), float(ea[-1])]}
    rho = rigorous_form(A, va[:, 0]) / float(np.dot(va[:, 0], va[:, 0]))
    out['high_block_min_rayleigh_upper'] = upper(rho)
    A0 = sub(F, hi, hi)
    e0, v0 = np.linalg.eigh((to_float(A0) + to_float(A0).T) / 2)
    rho0 = rigorous_form(A0, v0[:, 0]) / float(np.dot(v0[:, 0], v0[:, 0]))
    out['unshifted_high_block_rayleigh'] = rho0.str(8)
    out['fixed_quarter_high_gap'] = {
        'law': 'lambda_min(A_eps) >= 1/4 persists at this state (reconstructed reading of the continued 1/4 high-gap law)',
        'status': 'FALSIFIED_BOUND' if rho < rational_arb(Fraction(1, 4)) else 'NOT_REFUTED_BY_THIS_WITNESS',
        'witness_rayleigh_upper': upper(rho)}
    # reported constants first, then the floating-suggested ones
    candidates = []
    if reported is not None:
        candidates.append((reported_label, reported[0], reported[1]))
    if ea[0] > 0:
        candidates.append(('SUGGESTED', rational_below(0.98 * ea[0], 10 ** 6), rational_above(1.02 * ea[-1])))
    bounds = None
    out['high_block_bounds'] = []
    for label, a, b in candidates:
        ca = certify_psd(A - identity(n - k, rational_arb(a)), min(a / 50, Fraction(1, 1000))) \
            if ea[0] > float(a) else {'status': 'FALSIFIED_BOUND', 'reason': 'floating lambda_min(A) below a'}
        if ea[0] <= float(a) and upper(rho) < float(a):
            ca = {'status': 'FALSIFIED_BOUND', 'reason': 'rigorous Rayleigh upper bound below a',
                  'rayleigh_upper': upper(rho)}
        cb = certify_psd(identity(n - k, rational_arb(b)) - A, Fraction(1, 1000)) if ea[-1] < float(b) \
            else {'status': 'FALSIFIED_BOUND', 'reason': 'floating lambda_max(A) above b'}
        out['high_block_bounds'].append({'label': label, 'a': str(a), 'b': str(b),
                                         'a_le_A': ca['status'], 'A_le_b': cb['status']})
        if bounds is None and ca['status'] == 'CERTIFIED':
            bounds = (label, a, b, cb['status'])
    # scalar inverse-gap surrogate, refuted at the rigorous Rayleigh value
    Df = to_float(D)
    rho_q = Fraction(upper(rho)) if upper(rho) > 0 else None
    if rho_q is not None:
        Sf = (Df + Df.T) / 2 - Cf @ Cf.T / float(rho_q)
        es, vs = np.linalg.eigh(Sf)
        CC = C * C.transpose()
        w = rigorous_form(D - CC * (1 / rational_arb(rho_q)), vs[:, 0]) / float(np.dot(vs[:, 0], vs[:, 0]))
        out['scalar_gap'] = {
            'witness_rayleigh_value': w.str(10),
            'status': 'FALSIFIED_BOUND' if w < 0 else 'NOT_REFUTED_BY_THIS_WITNESS',
            'statement': 'for every scalar a with 0 < a <= lambda_min(A): D - a^-1 C C^T is not PSD'
                         if w < 0 else 'no refutation',
            'reason': 'a <= lambda_min(A) <= rho gives D - CC^T/a <= D - CC^T/rho; the witness is negative for the latter'}
    else:
        out['scalar_gap'] = {'status': 'NOT_ELIGIBLE', 'reason': 'high block not positive at this tolerance'}
    # coupling-preserving polynomial certificate
    if bounds is None:
        out['polynomial'] = {'status': 'NOT_ELIGIBLE', 'reason': 'no certified 0 < a I <= A <= b I'}
    else:
        label, a, b, cap = bounds
        R = np.eye(n - k) - Af / float(b)
        P, term = np.zeros_like(R), np.eye(n - k)
        for _ in range(degree):
            P += term
            term = term @ R
        P /= float(b)
        Xf = P @ Cf.T
        X = from_float(Xf)
        Ct = C.transpose()
        resid = Ct - A * X
        CX = C * X
        S = D - CX - CX.transpose() + X.transpose() * A * X - resid.transpose() * resid * (1 / rational_arb(a))
        Sf = to_float(S)
        es = np.linalg.eigvalsh((Sf + Sf.T) / 2)
        if es[0] > 0:
            cs = certify_psd(S, rational_below(es[0] / 2, 10 ** 9) or Fraction(1, 10 ** 12))
        else:
            cs = {'status': 'FALSIFIED_BOUND', 'reason': 'floating minimum of the certificate form is negative'}
            v = np.linalg.eigh((Sf + Sf.T) / 2)[1][:, 0]
            wv = rigorous_form(S, v)
            if wv < 0:
                cs['rigorous_negative_value'] = wv.str(10)
            else:
                cs['status'] = 'UNKNOWN_PRECISION'
        out['polynomial'] = {'bounds_used': label, 'a': str(a), 'b': str(b), 'degree': degree,
                             'X_sha256': array_sha256(Xf), 'R_sha256': array_sha256(to_float(resid)),
                             'upper_cap_status': cap,
                             'upper_cap_role': 'parameter of X only; blockEnergy_nonneg_of_inverse_residual_certificate assumes no upper bound on A',
                             'q_power_over_a': float((1 - a / b)) ** degree / float(a),
                             'certificate_floating_min': float(es[0]), **cs,
                             'consumer': 'Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_inverse_residual_certificate'}
    out['native_form'] = certify_psd(B, eps / 2)
    out['interpretation'] = ('A refuted surrogate is a failure of that sufficient estimate. It is a failure of the '
                             'native form only if the direct certificate of B also fails with a rigorous negative vector.')
    return out


CONSTRAINTS = {'even': ['physical M0 = 0', 'physical M2 = 0 (M1 = 0 by parity)', 'even pole functional = 0', 'physical M4 = 0'],
               'odd': ['physical M1 = 0 (M0 = M2 = 0 by parity)', 'odd pole functional = 0', 'physical M3 = 0', 'physical M5 = 0']}


def budget_records(record: dict) -> list[dict]:
    """BUDGET_SCHEMA records for every block test of one run, failures included."""
    st = record['state']
    state = {'source': {'definition': 'canonicalSourceMatrix', 'version_sha256': record['source']['backend_sha256'],
                        'prime_power_list_sha256': record['hashes']['prime_power_list_sha256']},
             'aperture': {'L_exact': st['L_exact']},
             'cutoff': {'expression': 'originalDetectorQuarticCutoff(L)=ceil(L^4)', 'value': st['K']},
             'parity': st['parity'],
             'carrier': {'name': st['carrier'], 'dimension': st['dimension'], 'constraints': CONSTRAINTS[st['parity']]},
             'metric': {'kind': 'PHYSICAL_INHERITED_EUCLIDEAN', 'gram_sha256': record['hashes']['gram_sha256']},
             'state_kind': 'ACTUAL_STATE'}
    out = []
    for b in record.get('block_tests', []):
        poly = b['polynomial']
        eligible = 'X_sha256' in poly
        disposition = poly['status'] if poly['status'] in DISPOSITIONS else 'UNKNOWN_PRECISION'
        out.append({
            'state': state,
            'partition': {
                'blocks': [{'name': 'D', 'kind': 'Fourier-prefix moment slice through the split', 'dimension': b['low_dimension']},
                           {'name': 'A', 'kind': 'W-orthogonal complement inside the slice', 'dimension': b['high_dimension']}],
                'coupling_blocks': [{'name': 'C', 'rows': 'D', 'columns': 'A', 'retained': 'COMPLETE'}],
                'inverse_domain': 'A >= a I certified; X = P_m(A) C^T, P_m(A) = b^-1 sum_{j<m} (I - A/b)^j',
                'trial_inverse_X_sha256': poly.get('X_sha256', 'NOT_ELIGIBLE'),
                'residual_R_sha256': poly.get('R_sha256', 'NOT_ELIGIBLE')},
            'enclosure': {'representation': 'OUTWARD_ROUNDED_INTERVALS_WITH_PROOF',
                          'entry_error': 'Arb balls at %d bits from the repository equation-(4.4) backend' % record['precision_bits'],
                          'coordinate_error': 'exact: floating proposal corrected in Arb on four pivots; C Y = 0 enclosed',
                          'inverse_response_error': 'exact X (floating proposal); residual R = C^T - A X enclosed in Arb'},
            'budget': {'retained_diagonal': 'D (complete low block of F + eps G)',
                       'full_inverse_response': 'C X + X^T C^T - X^T A X',
                       'residual_allowance': 'a^-1 R^T R with a = %s' % poly.get('a', 'n/a'),
                       'E_err': 'shifted factorization residual, Frobenius bound %s' % poly.get('residual_frobenius_upper', poly.get('rigorous_negative_value', 'n/a')),
                       'physical_margin': ('Q_p >= -%s ||x||^2 on the slice' % b['target_tolerance']) if disposition == 'CERTIFIED' else None,
                       'certificate_form_lower_eigenvalue_coordinates': poly.get('certified_lower_eigenvalue') if eligible else None,
                       'tolerance': b['target_tolerance']},
            'disposition': disposition,
        })
    return out


def compare_principal_entries(path: Path, bits: int = 256) -> dict:
    """Overlap check of external exact-rational principal entries with the Arb source."""
    raw = Path(path).read_bytes()
    data = json.loads(raw)
    if data.get('parity') != 'even':
        raise ValueError('only even principal entries are supported')
    L = Fraction(data['L'])
    st = NativeState(L, K=int(data['K']), bits=bits)
    if st.Q != int(data['Q']):
        raise ArithmeticError('external prime cutoff differs')
    E = data['E']
    scale = 1 << int(E['bits'])
    n = len(E['center'])
    worst, overlaps = 0.0, 0
    for i in range(n):
        for j in range(n):
            if i == 0 and j == 0:
                mine = st.entry(0, 0)
            elif i == 0 or j == 0:
                mine = 2 * st.entry(0, max(i, j))
            else:
                mine = 2 * (st.entry(i, j) + st.entry(i, -j))
            c, r = int(E['center'][i][j]), int(E['radius'][i][j])
            lo, hi = rational_arb(Fraction(c - r, scale)), rational_arb(Fraction(c + r, scale))
            ext = (lo + hi) / 2
            ext = ext.union(lo).union(hi)
            if mine.overlaps(ext):
                overlaps += 1
            worst = max(worst, abs(float((mine - ext).mid())))
    return {'schema': 'OPICA4_ARITHMETIC_FRONTIER_ENTRY_CROSSCHECK_V1', **CAPS,
            'external_sha256': hashlib.sha256(raw).hexdigest(), 'L': str(L), 'K': st.K, 'Q': st.Q,
            'entries': n * n, 'overlapping': overlaps, 'max_midpoint_difference': worst,
            'status': 'ALL_OVERLAP' if overlaps == n * n else 'MISMATCH',
            'scope': 'Two independent constructions of the same even-reduced canonical entries; overlap is consistency evidence, not a proof of either backend.'}


F2 = Fraction
CAMPAIGN = {
    # archived small-aperture point statements (native endpoint archive)
    'archive_L2_even': dict(L=F2(2), parity='even', bits=192, bracket=True, margins=[F2(1, 2 ** 64)]),
    'archive_L2_odd': dict(L=F2(2), parity='odd', bits=192, bracket=True, margins=[F2(1, 2 ** 64)]),
    'archive_L9_4_even': dict(L=F2(9, 4), parity='even', bits=256, bracket=True, margins=[F2(1, 2 ** 100)]),
    'archive_L9_4_odd': dict(L=F2(9, 4), parity='odd', bits=256, bracket=True, margins=[F2(1, 2 ** 100)]),
    'archive_L5_2_even': dict(L=F2(5, 2), parity='even', bits=320, bracket=True, margins=[F2(1, 2 ** 146)]),
    'archive_L5_2_odd': dict(L=F2(5, 2), parity='odd', bits=320, bracket=True, margins=[F2(1, 2 ** 146)]),
    # reported L=4 endpoint and block statements, and the C1 checkpoints n=2,3,4
    'L4_even': dict(L=F2(4), parity='even', bits=192, eps_list=[F2(1, 2), F2(1, 1024)], split=128),
    'L4_odd': dict(L=F2(4), parity='odd', bits=192, eps_list=[F2(1, 2), F2(1, 1024)], split=128),
    'L4_even_bracket': dict(L=F2(4), parity='even', bits=1024, bracket=True),
    'L4_odd_bracket': dict(L=F2(4), parity='odd', bits=1024, bracket=True),
    'L5_even': dict(L=F2(5), parity='even', bits=192, eps_list=[F2(1, 3), F2(1, 1024)], split=312),
    'L5_odd': dict(L=F2(5), parity='odd', bits=192, eps_list=[F2(1, 3), F2(1, 1024)], split=312),
    'EH6_L6_even': dict(L=F2(6), parity='even', bits=192, eps_list=[F2(1, 4)], split=648),
    'EH6_L6_odd': dict(L=F2(6), parity='odd', bits=192, eps_list=[F2(1, 4)], split=648),
}


def run_campaign(out_dir: Path, names: list[str]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    for name in names:
        rec = slice_run(**CAMPAIGN[name])
        rec['campaign_entry'] = name
        (out_dir / (name + '.json')).write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
        print(json.dumps({'entry': name, 'certificates': [c['status'] for c in rec['endpoint_certificates']],
                          'seconds': rec['seconds']}), flush=True)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--campaign', help='comma-separated campaign entries, or "all"')
    p.add_argument('--out-dir', type=Path)
    p.add_argument('--crosscheck', type=Path, help='external even principal-entry file (data only)')
    p.add_argument('--L', help='exact rational aperture, e.g. 4 or 5/2')
    p.add_argument('--parity', choices=('even', 'odd'))
    p.add_argument('--eps', action='append', default=[], help='tolerance, repeatable')
    p.add_argument('--margin', action='append', default=[], help='positive margin')
    p.add_argument('--split', type=int, help='Fourier-prefix flag split for the block tests')
    p.add_argument('--bits', type=int, default=192)
    p.add_argument('--ldl', action='store_true')
    p.add_argument('--K', type=int)
    p.add_argument('--bracket', action='store_true', help='rigorous two-sided bracket of the slice bottom')
    p.add_argument('--out', type=Path)
    a = p.parse_args(argv)
    if a.campaign:
        names = list(CAMPAIGN) if a.campaign == 'all' else a.campaign.split(',')
        run_campaign(a.out_dir, names)
        return 0
    if a.crosscheck:
        rec = compare_principal_entries(a.crosscheck, bits=a.bits)
        a.out.write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
        return 0 if rec['status'] == 'ALL_OVERLAP' else 1
    rec = slice_run(Fraction(a.L), a.parity, [Fraction(e) for e in a.eps], a.split, a.bits,
                    a.ldl, [Fraction(m) for m in a.margin], a.K, a.bracket)
    a.out.write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'parity': a.parity, 'L': a.L, 'K': rec['state']['K'], 'dim': rec['state']['dimension'],
                      'certificates': [c['status'] for c in rec['endpoint_certificates']], 'seconds': rec['seconds']}))
    return 0 if all(c['status'] == 'CERTIFIED' for c in rec['endpoint_certificates']) else 1


if __name__ == '__main__':
    sys.exit(main())
