"""Certified bottom eigenvalue of the native canonical form on a constrained space.

Everything is ball arithmetic (python-flint Arb); there is no floating-point
step. For one native state and one constrained parity space the tool forms the
pencil ``(G, N)`` with ``G = B^T E B`` and ``N = B^T W B`` (``B`` a ball basis of
the constraint null space, ``E`` the reduced canonical matrix, ``W`` the physical
weights) and uses Sylvester inertia of ``G - mu N`` from an ``LDL^T``
factorization whose pivots are all certified non-zero. The number of negative
pivots is then the exact number of pencil eigenvalues below ``mu`` for every
matrix inside the entry balls.

A certificate consists of exact decimal numbers ``lo < hi < mu2`` with

* no eigenvalue below ``lo``, at least one below ``hi``  (bottom in ``[lo, hi)``);
* exactly one eigenvalue below ``mu2``                    (the bottom is simple).

``verify`` re-derives these three counts from the stored numbers. ``certify``
finds the numbers by geometric search and bisection on the same counts.

Scope: one aperture, one cutoff, one parity, one constrained space. A positive
certified bottom is a statement about that finite object. It says nothing about
another aperture, a limiting form, or RH. RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent
SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_BOTTOM_CERTIFICATE_V1'
SPACES = {
    'even': {'full': [], 'flat_pole_neutral': [0, 1, 2], 'moment_slice': [0, 1, 2, 3]},
    'odd': {'full': [], 'flat_pole_neutral': [0, 1], 'moment_slice': [0, 1, 2, 3]},
}


class CertificateFailure(ArithmeticError):
    """A count could not be certified, or a stored certificate does not verify."""


def check(value: bool, message: str) -> None:
    if not value:
        raise CertificateFailure(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_source():
    spec = importlib.util.spec_from_file_location('_frontier_native_source_bottom', HERE / 'native_source.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def null_basis(C, rows: list[int], n: int) -> list[list[arb]]:
    """Ball basis of ``{x : C[rows] x = 0}`` with pivots ``0..r-1`` and free coordinates ``r..n-1``."""
    r = len(rows)
    if r == 0:
        return [[arb(1) if k == j else arb(0) for k in range(n)] for j in range(n)]
    A = arb_mat(r, r, [C[i, j] for i in rows for j in range(r)])
    basis = []
    for j in range(r, n):
        s = A.solve(arb_mat(r, 1, [-C[i, j] for i in rows]))
        basis.append([s[i, 0] for i in range(r)] + [arb(1) if k == j else arb(0) for k in range(r, n)])
    return basis


def gram(M, vectors: list[list[arb]], n: int) -> list[list[arb]]:
    images = [[sum((M[a, b] * v[b] for b in range(n)), arb(0)) for a in range(n)] for v in vectors]
    d = len(vectors)
    return [[sum((vectors[i][a] * images[j][a] for a in range(n)), arb(0)) for j in range(d)] for i in range(d)]


def pencil(state, parity: str, space: str):
    """``(G, N)`` of the canonical form and the physical norm on the constrained space."""
    E, w = state.reduced(parity)
    C = state.constraints(parity)
    n = len(w)
    B = null_basis(C, SPACES[parity][space], n)
    W = arb_mat(n, n, [arb(w[i]) if i == j else arb(0) for i in range(n) for j in range(n)])
    return gram(E, B, n), gram(W, B, n), B, w


def count_below(G, N, mu: arb) -> int:
    """Certified number of eigenvalues of the pencil ``(G, N)`` below ``mu``."""
    d = len(G)
    A = [[G[i][j] - mu * N[i][j] for j in range(d)] for i in range(d)]
    negatives = 0
    for k in range(d):
        pivot = A[k][k]
        check(not pivot.contains(0), 'pivot not separated from zero')
        if pivot < 0:
            negatives += 1
        for i in range(k + 1, d):
            factor = A[i][k] / pivot
            for j in range(k + 1, d):
                A[i][j] = A[i][j] - factor * A[k][j]
    return negatives


def exact(value: arb, digits: int) -> str:
    """A decimal string for the midpoint; the string is the exact number that is stored and reused."""
    return value.mid().str(digits, radius=False)


def robust_count(G, N, mu: arb, digits: int) -> tuple[int, str]:
    """Count below a nearby exact decimal; nudges ``mu`` if a pivot ball meets zero."""
    for step in range(6):
        text = exact(mu * (1 + arb(step) / 2 ** 24), digits)
        try:
            return count_below(G, N, arb(text)), text
        except CertificateFailure:
            continue
    raise CertificateFailure('no certified count near the requested value')


def certify_pencil(G, N, digits: int = 40, relative: Fraction = Fraction(1, 10 ** 6)) -> dict:
    """Bracket the bottom eigenvalue and certify that it is simple (positive bottoms only)."""
    d = len(G)
    check(d >= 1, 'empty space')
    check(count_below(G, N, arb(0)) == 0, 'the form is not certified positive definite on this space')
    hi = G[0][0] / N[0][0] * 2
    n_hi, hi_text = robust_count(G, N, hi, digits)
    check(n_hi >= 1, 'upper start is not above the bottom')
    lo, lo_text = hi, hi_text
    for _ in range(64):
        n_lo, lo_text = robust_count(G, N, arb(lo_text) / 2 ** 24, digits)
        if n_lo == 0:
            break
        hi_text = lo_text
    else:
        raise CertificateFailure('no lower bracket found')
    tolerance = 1 + arb(relative.numerator) / relative.denominator
    for _ in range(200):
        if bool(arb(hi_text) < arb(lo_text) * tolerance):
            break
        n_mid, mid_text = robust_count(G, N, (arb(lo_text) * arb(hi_text)).sqrt(), digits)
        if n_mid == 0:
            lo_text = mid_text
        else:
            hi_text = mid_text
    else:
        raise CertificateFailure('bisection did not converge')
    record = {'dim': d, 'lo': lo_text, 'hi': hi_text, 'below_lo': 0,
              'below_hi': count_below(G, N, arb(hi_text)), 'mu2': None, 'below_mu2': None, 'simple': None}
    if d > 1:
        mu2_text = None
        candidate = arb(hi_text)
        for _ in range(400):
            candidate = candidate * 4
            n_c, c_text = robust_count(G, N, candidate, digits)
            if n_c == 1:
                mu2_text = c_text
            elif n_c >= 2:
                break
        if mu2_text is None:
            n_c, c_text = robust_count(G, N, arb(hi_text) * (1 + arb(1) / 1024), digits)
            mu2_text = c_text if n_c == 1 else None
        record['mu2'] = mu2_text
        record['below_mu2'] = None if mu2_text is None else count_below(G, N, arb(mu2_text))
        record['simple'] = bool(record['below_hi'] == 1 and record['below_mu2'] == 1)
    else:
        record['simple'] = True
    return record


def ground_vector(G, N, B, w, lo_text: str, digits: int) -> dict:
    """Two inverse iterations at ``lo`` and the certified Rayleigh quotient of the stored vector."""
    d = len(G)
    n = len(w)
    shift = arb(lo_text)
    A = arb_mat(d, d, [G[i][j].mid() - shift * N[i][j].mid() for i in range(d) for j in range(d)])
    Nm = arb_mat(d, d, [N[i][j].mid() for i in range(d) for j in range(d)])
    y = arb_mat(d, 1, [arb(1)] * d)
    for _ in range(3):
        y = A.solve(Nm * y)
        scale = max(abs(y[i, 0].mid()) for i in range(d))
        y = arb_mat(d, 1, [(y[i, 0] / scale).mid() for i in range(d)])
    stored = [exact(y[i, 0], digits) for i in range(d)]
    yb = [arb(s) for s in stored]
    num = sum((yb[i] * G[i][j] * yb[j] for i in range(d) for j in range(d)), arb(0))
    den = sum((yb[i] * N[i][j] * yb[j] for i in range(d) for j in range(d)), arb(0))
    rq = num / den
    xs = [sum((B[j][a] * yb[j] for j in range(d)), arb(0)) for a in range(n)]
    norm = sum((arb(w[a]) * xs[a] * xs[a] for a in range(n)), arb(0)).sqrt()
    return {'pencil_vector': stored, 'rayleigh_quotient_enclosure': rq.str(20),
            'rayleigh_upper': exact(rq.upper() * (1 + arb(1) / 10 ** 12), 24),
            'reduced_unit_vector': [exact(x / norm, digits) for x in xs]}


def certify_state(L: Fraction, K: int | None, bits: int, with_vectors: bool = True) -> dict:
    src = load_source()
    state = src.NativeState(L, K=K, bits=bits)
    ctx.prec = bits
    digits = max(40, int(bits * 0.30))
    out = {'schema': SCHEMA, 'RH': 'OPEN', 'Step4': 'OPEN', 'L': str(Fraction(L)), 'K': state.K, 'bits': bits,
           'prime_cutoff': state.Q, 'tool_sha256': sha256(Path(__file__)),
           'native_source_sha256': sha256(HERE / 'native_source.py'),
           'claim': 'FINITE_CERTIFICATE_ONE_STATE_ONE_SPACE_NOT_A_STATEMENT_ABOUT_ANOTHER_APERTURE_OR_RH',
           'spaces': {}}
    for parity, table in SPACES.items():
        for space in table:
            G, N, B, w = pencil(state, parity, space)
            if not G:
                continue
            record = certify_pencil(G, N, digits)
            if with_vectors:
                record.update(ground_vector(G, N, B, w, record['lo'], digits))
            out['spaces'][parity + '/' + space] = record
    return out


def verify_state(record: dict, state=None) -> dict:
    """Re-derive every stored count (and Rayleigh bound) from the stored exact numbers."""
    check(record.get('schema') == SCHEMA and record.get('RH') == record.get('Step4') == 'OPEN', 'wrong record')
    if state is None:
        state = load_source().NativeState(Fraction(record['L']), K=record['K'], bits=record['bits'])
    ctx.prec = record['bits']
    seen = {}
    for name, row in record['spaces'].items():
        parity, space = name.split('/')
        G, N, _, _ = pencil(state, parity, space)
        check(len(G) == row['dim'], 'dimension differs')
        lo, hi = arb(row['lo']), arb(row['hi'])
        check(bool(arb(0) < lo) and bool(lo < hi), 'bracket is not positive and ordered')
        check(count_below(G, N, lo) == 0, 'an eigenvalue lies below the stored lower bound')
        below_hi = count_below(G, N, hi)
        check(below_hi >= 1 and below_hi == row['below_hi'], 'upper bracket count differs')
        simple = True
        if row['mu2'] is not None:
            mu2 = arb(row['mu2'])
            check(bool(hi < mu2) and count_below(G, N, mu2) == 1 and below_hi == 1, 'bottom is not certified simple')
        else:
            simple = row['dim'] == 1
        check(simple == row['simple'], 'simplicity flag differs')
        if 'pencil_vector' in row:
            y = [arb(s) for s in row['pencil_vector']]
            d = len(y)
            num = sum((y[i] * G[i][j] * y[j] for i in range(d) for j in range(d)), arb(0))
            den = sum((y[i] * N[i][j] * y[j] for i in range(d) for j in range(d)), arb(0))
            rq = num / den
            check(bool(lo < rq) and bool(rq < arb(row['rayleigh_upper'])), 'stored vector does not reproduce its Rayleigh bound')
        seen[name] = {'lo': row['lo'], 'hi': row['hi'], 'simple': simple}
    return seen


def main(argv: list[str]) -> int:
    """``bottom_certificate.py L BITS OUT [K] [--no-vectors]``."""
    with_vectors = '--no-vectors' not in argv
    argv = [a for a in argv if a != '--no-vectors']
    L, bits, out = Fraction(argv[1]), int(argv[2]), Path(argv[3])
    K = int(argv[4]) if len(argv) > 4 else None
    record = certify_state(L, K, bits, with_vectors=with_vectors)
    verify_state(record)
    out.write_bytes((json.dumps(record, indent=1) + '\n').encode())
    for name, row in record['spaces'].items():
        print(f"{name:24s} dim={row['dim']:3d} bottom in [{row['lo'][:14]}, {row['hi'][:14]}) simple={row['simple']}")
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
