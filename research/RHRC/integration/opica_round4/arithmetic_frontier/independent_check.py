"""Independent floating-point-free checker for small native moment-slice claims.

This checker shares only the equation-(4.4) primitives with the replay engine
``native_slice.py``. It takes the repository's *direct* full canonical matrix
``canonical_source_matrix(L, K, Q)`` (signed indices), compresses it to the
parity space itself, writes the Lean slice equations independently, uses an
exact elimination basis (no proposal from floating linear algebra), and
certifies a margin by interval LDL^T in Arb. A margin is refuted by an exact
inverse-iteration vector whose Rayleigh quotient lies below it.

It needs only python-flint and sympy, so it runs in the hash-locked CI
environment. It is research certification, not Lean authority. RH and Step 4
remain OPEN.
"""
from __future__ import annotations

import importlib.util
import math
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_mat, ctx, fmpq

REPO = Path(__file__).resolve().parents[5]
BACKEND_PATH = REPO / 'research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py'


def backend():
    spec = importlib.util.spec_from_file_location('_frontier_independent_backend', BACKEND_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def q(x: Fraction | int) -> arb:
    x = Fraction(x)
    return arb(fmpq(x.numerator, x.denominator))


def quartic_cutoff(L: Fraction) -> int:
    p = Fraction(L) ** 4
    return -((-p.numerator) // p.denominator)


def full_matrix(L: Fraction, bits: int):
    ctx.prec = bits
    b = backend()
    K = quartic_cutoff(L)
    Q = int(math.floor(math.exp(float(L))))
    La = q(L)
    if not b.fixed_cell_membership(Q, La)['certified']:
        raise ArithmeticError('aperture not certified in one prime cell')
    return b.canonical_source_matrix(La, K, Q), K, Q


def parity_space(M: arb_mat, K: int, parity: str):
    """Columns of the injection z -> x (x_{+-a} = z_a or +-z_a) and the physical weights."""
    if parity == 'even':
        idx = list(range(0, K + 1))
        emb = lambda a, n: arb(1) if abs(n) == a else arb(0)
    else:
        idx = list(range(1, K + 1))
        emb = lambda a, n: (arb(1) if n == a else arb(-1) if n == -a else arb(0))
    J = arb_mat([[emb(a, n) for a in idx] for n in range(-K, K + 1)])
    return J, idx


def slice_equations(L: Fraction, K: int, parity: str) -> arb_mat:
    """Lean carrier: boundary-flat moments, native pole functional and the slice moments, on full indices."""
    La, pi = q(L), arb.pi()
    ns = range(-K, K + 1)
    d = lambda n: La ** 2 + 16 * pi ** 2 * n * n
    if parity == 'even':
        rows = [[arb(n) ** k for n in ns] for k in (0, 1, 2)]
        rows.append([La / d(n) for n in ns])
        rows.append([arb(n) ** 4 for n in ns])
    else:
        rows = [[arb(n) ** k for n in ns] for k in (0, 1, 2)]
        rows.append([4 * pi * n / d(n) for n in ns])
        rows.append([arb(n) ** 3 for n in ns])
        rows.append([arb(n) ** 5 for n in ns])
    return arb_mat(rows)


def elimination_basis(C: arb_mat) -> arb_mat:
    """Exact kernel basis: free unit columns corrected on the last r pivot columns.

    Rows of C that vanish identically on the parity space are dropped first; the
    remaining r rows are independent, which the solve certifies.
    """
    keep = [i for i in range(C.nrows()) if not all(C[i, j].is_zero() for j in range(C.ncols()))]
    C = arb_mat([[C[i, j] for j in range(C.ncols())] for i in keep])
    r, n = C.nrows(), C.ncols()
    piv = list(range(n - r, n))
    free = list(range(0, n - r))
    Cp = arb_mat([[C[i, j] for j in piv] for i in range(r)])
    Cf = arb_mat([[C[i, j] for j in free] for i in range(r)])
    S = Cp.solve(-Cf)
    rows = [[arb(1) if j == i else arb(0) for j in range(len(free))] for i in range(len(free))]
    rows += [[S[i, j] for j in range(len(free))] for i in range(r)]
    return arb_mat(rows)


def ldl_positive(A: arb_mat) -> tuple[bool, int]:
    n = A.nrows()
    M = [row[:] for row in A.tolist()]
    for k in range(n):
        p = M[k][k]
        if not (p > 0):
            return False, k
        for i in range(k + 1, n):
            f = M[i][k] / p
            for j in range(k + 1, i + 1):
                M[i][j] = M[i][j] - f * M[j][k]
    return True, n


def slice_forms(L: Fraction, parity: str, bits: int):
    M, K, Q = full_matrix(L, bits)
    J, idx = parity_space(M, K, parity)
    E = J.transpose() * M * J
    W = J.transpose() * J
    C = slice_equations(L, K, parity) * J
    Y = elimination_basis(C)
    if not all((C * Y)[i, j].contains(0) for i in range(C.nrows()) for j in range(Y.ncols())):
        raise ArithmeticError('elimination basis is not inside the slice')
    F = Y.transpose() * E * Y
    G = Y.transpose() * W * Y
    return {'F': F, 'G': G, 'K': K, 'Q': Q, 'dimension': Y.ncols(), 'Y': Y, 'E': E, 'W': W}


def check_margin(L: Fraction, parity: str, margin: Fraction, bits: int, iterations: int = 6) -> dict:
    """CERTIFIED by interval LDL of F - mG, or FALSIFIED by an exact vector below m."""
    forms = slice_forms(L, parity, bits)
    F, G = forms['F'], forms['G']
    ok, k = ldl_positive(F - q(margin) * G)
    out = {'L': str(Fraction(L)), 'parity': parity, 'K': forms['K'], 'Q': forms['Q'],
           'dimension': forms['dimension'], 'margin': str(margin), 'bits': bits,
           'RH': 'OPEN', 'Step4': 'OPEN', 'authority': 'INDEPENDENT_RESEARCH_CHECK_NOT_LEAN_AUTHORITY'}
    Fm = arb_mat([[x.mid() for x in row] for row in F.tolist()])
    Gm = arb_mat([[x.mid() for x in row] for row in G.tolist()])
    x = arb_mat([[arb(1)] for _ in range(F.nrows())])
    for _ in range(iterations):
        y = Fm.solve(Gm * x, algorithm='approx')
        s = (y.transpose() * y)[0, 0].mid().sqrt().mid()
        x = arb_mat([[(y[i, 0] / s).mid()] for i in range(y.nrows())])
    rho = (x.transpose() * F * x)[0, 0] / (x.transpose() * G * x)[0, 0]
    out['rayleigh_upper'] = rho.str(8)
    if ok:
        out['status'] = 'CERTIFIED'
    elif rho < q(margin):
        out['status'] = 'FALSIFIED_BOUND'
    else:
        out['status'] = 'UNKNOWN_PRECISION'
        out['failed_pivot'] = k
    return out


# ----------------------------------------------------------------------------- large states (Increment 2B)

def _load_sibling(name: str, file: str):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).resolve().parent / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def spread_pivots(n: int, r: int) -> list[int]:
    """r distinct pivot columns spread over [0, n): well-conditioned interpolation nodes."""
    piv = sorted({min(n - 1, max(0, round((j + 1) * (n - 1) / r))) for j in range(r)})
    j = n - 1
    while len(piv) < r:
        if j not in piv:
            piv.append(j)
        j -= 1
    return sorted(piv)


def elimination_basis_on(C: arb_mat, pivots: list[int]) -> arb_mat:
    """Exact kernel basis: unit columns on the free indices, solved on the pivots."""
    r, n = C.nrows(), C.ncols()
    free = [j for j in range(n) if j not in pivots]
    Cp = arb_mat([[C[i, j] for j in pivots] for i in range(r)])
    Cf = arb_mat([[C[i, j] for j in free] for i in range(r)])
    S = Cp.solve(-Cf)
    rows = [[arb(0)] * len(free) for _ in range(n)]
    for c, j in enumerate(free):
        rows[j][c] = arb(1)
    for k, p in enumerate(pivots):
        rows[p] = [S[k, c] for c in range(len(free))]
    return arb_mat(rows)


def reconstruct_checkpoint(L: Fraction, parity: str, eps: Fraction, bits: int = 192, block: int = 96) -> dict:
    """Level-3 reconstruction of Q_p(L,x) >= -eps ||x||^2 on the whole slice, numpy-free.

    Shared trust boundary: the vectorized assembly in native_source.py (the same
    equation-(4.4) backend primitives as the engine). Independent of the engine:
    the exact elimination basis (spread pivots, no floating proposal), the Gram
    and form products, and the blocked interval Schur certificate.
    """
    import time
    t0 = time.time()
    SRC = _load_sibling('_frontier_native_source_check', 'native_source.py')
    KER = _load_sibling('_frontier_certificates_check', 'certificates.py')
    st = SRC.NativeState(Fraction(L), bits=bits)
    KER.validate_state(st.Lq, st.K, st.Q, [p for p, _ in st.atoms])
    E, w = st.reduced(parity)
    C = st.constraints(parity)
    piv = spread_pivots(C.ncols(), C.nrows())
    Y = elimination_basis_on(C, piv)
    if not KER.in_kernel(C, Y):
        raise ArithmeticError('elimination basis inconsistent with the slice equations')
    W = arb_mat([[arb(w[i]) if i == j else arb(0) for j in range(len(w))] for i in range(len(w))])
    F = Y.transpose() * E * Y
    G = Y.transpose() * W * Y
    gram = KER.certify_block_ldl(G, block)
    cert = KER.certify_block_ldl(F + q(eps) * G, block)
    dim = Y.ncols()
    expected = st.K - (3 if parity == 'even' else 4)
    return {'schema': 'OPICA4_ARITHMETIC_FRONTIER_INDEPENDENT_RECONSTRUCTION_V1', 'RH': 'OPEN', 'Step4': 'OPEN',
            'authority': 'INDEPENDENT_RESEARCH_CHECK_NOT_LEAN_AUTHORITY', 'assurance_level': 'LEVEL_3_INDEPENDENT_BASIS_AND_CERTIFICATE_SHARED_SOURCE_ASSEMBLY',
            'shared_trust_boundary': ['native_source.py vectorized assembly', 'canonical_source_arb.py equation-(4.4) primitives'],
            'L': str(st.Lq), 'K': st.K, 'Q': st.Q, 'parity': parity, 'dimension': dim, 'dimension_expected': expected,
            'tolerance': str(eps), 'bits': bits, 'pivots': piv,
            'statement': 'Q_p(L,x) >= -%s ||x||^2 for every x in the slice (physical norm)' % eps,
            'gram_rank_certificate': gram, 'certificate': cert,
            'status': 'CERTIFIED' if (cert['status'] == 'CERTIFIED' and gram['status'] == 'CERTIFIED' and dim == expected) else 'UNKNOWN_PRECISION',
            'hashes': {'gram_enclosure_sha256': KER.enclosure_sha256(G), 'native_source_sha256': SRC.sha256(Path(__file__).resolve().parent / 'native_source.py'),
                       'kernel_sha256': SRC.sha256(Path(__file__).resolve().parent / 'certificates.py'),
                       'checker_sha256': SRC.sha256(Path(__file__)), 'backend_sha256': SRC.sha256(SRC.BACKEND_PATH)},
            'seconds': round(time.time() - t0, 1)}


def main(argv=None) -> int:
    import argparse, json
    p = argparse.ArgumentParser(description='Level-3 numpy-free reconstruction of one checkpoint')
    p.add_argument('--L', required=True)
    p.add_argument('--parity', choices=('even', 'odd'), required=True)
    p.add_argument('--eps', required=True)
    p.add_argument('--bits', type=int, default=192)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(argv)
    rec = reconstruct_checkpoint(Fraction(a.L), a.parity, Fraction(a.eps), a.bits)
    a.out.write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: rec[k] for k in ('L', 'parity', 'dimension', 'status', 'seconds')}))
    return 0 if rec['status'] == 'CERTIFIED' else 1


if __name__ == '__main__':
    raise SystemExit(main())
