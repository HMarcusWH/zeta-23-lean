"""Low-cutoff native energies: the prime side against the sum over zeta zeros.

On the pole-neutral boundary-flat parity spaces (the spaces the least-crossing
selector of ``Zeta23/CCM/NativeDeepThresholdGround.lean`` walks through) the
repository proves that the canonical quadratic form equals the Weil sum over the
nontrivial zeros (``zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm``).
In closed form, for a real parity vector with reduced coordinates ``x``,

    energy = (8/L) * sum_{gamma > 0} sin^2(gamma L / 2) * q(gamma)^2      (all zeros on the line)

    even:  q(gamma) = x_0/gamma + sum_a 2 x_a gamma / (gamma^2 - w_a^2)
    odd :  q(gamma) = 2 sum_a x_a w_a / (gamma^2 - w_a^2),                 w_a = 2 pi a / L.

This tool evaluates both sides in ball arithmetic: the prime side from
``native_source.py`` (enclosures of ``pole - arch - prime``) and the zero side
from a stored list of numerical zero ordinates, truncated. It also checks the
closed form of the two cutoff-3 vectors,

    even: q(g) = c_e (g^2 + 1/4) / (g prod_{a<=3} (g^2 - w_a^2)),
    odd : q(g) = c_o (g^2 + 1/4) /    prod_{a<=3} (g^2 - w_a^2).

The zero ordinates are input data, not certified enclosures, and the sum is
truncated; agreement is a consistency check of an identity already proved in
Lean (EXPERIMENTAL SIGNAL). It is not a statement about off-line zeros and not
evidence for or against RH. RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_SPECTRAL_LOWDEG_V1'
FLAT_ROWS = {'even': [0, 1, 2], 'odd': [0, 1]}


class SpectralFailure(ArithmeticError):
    """A stored spectral record does not reproduce."""


def check(value: bool, message: str) -> None:
    if not value:
        raise SpectralFailure(message)


def _load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BC = _load('_frontier_bottom_certificate_spectral', 'bottom_certificate.py')


def indices(parity: str, K: int) -> list[int]:
    return list(range(0, K + 1)) if parity == 'even' else list(range(1, K + 1))


def q_value(parity: str, vec: list[arb], idx: list[int], L: arb, g: arb) -> arb:
    pi = arb.pi()
    if parity == 'even':
        total = vec[0] / g
        for x, a in zip(vec[1:], idx[1:]):
            w = 2 * pi * a / L
            total += 2 * x * g / (g * g - w * w)
        return total
    total = arb(0)
    for x, a in zip(vec, idx):
        w = 2 * pi * a / L
        total += 2 * x * w / (g * g - w * w)
    return total


def zero_gram(parity: str, basis: list[list[arb]], K: int, L: arb, zeros: list[arb]) -> list[list[arb]]:
    idx = indices(parity, K)
    Q = [[q_value(parity, v, idx, L, g) for g in zeros] for v in basis]
    s2 = [(g * L / 2).sin() ** 2 for g in zeros]
    d = len(basis)
    return [[8 / L * sum((s2[k] * Q[i][k] * Q[j][k] for k in range(len(zeros))), arb(0)) for j in range(d)]
            for i in range(d)]


def pencil_bottom(G: list[list[arb]], N: list[list[arb]]) -> arb:
    """Smallest eigenvalue of a 1x1 or 2x2 pencil in closed form."""
    if len(G) == 1:
        return G[0][0] / N[0][0]
    check(len(G) == 2, 'closed form only for dimension one or two')
    a = N[0][0] * N[1][1] - N[0][1] * N[1][0]
    b = -(G[0][0] * N[1][1] + G[1][1] * N[0][0] - G[0][1] * N[1][0] - G[1][0] * N[0][1])
    c = G[0][0] * G[1][1] - G[0][1] * G[1][0]
    return (-b - (b * b - 4 * a * c).sqrt()) / (2 * a)


def compare_state(L: Fraction, K: int, bits: int, zeros: list[str]) -> dict:
    """Prime-side and zero-side bottoms of both parity spaces at cutoff ``K`` (3 or 4)."""
    check(K in (3, 4), 'cutoff must be 3 or 4')
    state = BC.load_source().NativeState(L, K=K, bits=bits)
    ctx.prec = bits
    gam = [arb(s) for s in zeros]
    row = {'L': str(Fraction(L)), 'K': K, 'bits': bits, 'prime_cutoff': state.Q, 'zeros_used': len(gam)}
    for parity in ('even', 'odd'):
        G, N, B, _ = BC.pencil(state, parity, 'flat_pole_neutral')
        Gz = zero_gram(parity, B, K, state.L, gam)
        prime, zero = pencil_bottom(G, N), pencil_bottom(Gz, N)
        check(bool(prime > 0) and bool(zero > 0), 'non-positive low-cutoff bottom')
        rel = abs(prime - zero) / prime
        row[parity] = {'dim': len(B), 'prime_side': BC.exact(prime, 30), 'prime_side_radius': prime.rad().str(3, radius=False),
                       'zero_side': BC.exact(zero, 30), 'relative_difference_upper': rel.upper().str(3, radius=False)}
    return row


def cutoff3_closed_form(L: Fraction, bits: int, samples: tuple[str, ...] = ('14.134725', '21.02204', '101.3', '0.777')) -> dict:
    """Ball check that both cutoff-3 vectors have the closed form above; returns the constants."""
    state = BC.load_source().NativeState(L, K=3, bits=bits)
    ctx.prec = bits
    pi = arb.pi()
    out = {}
    for parity in ('even', 'odd'):
        _, N, B, _ = BC.pencil(state, parity, 'flat_pole_neutral')
        check(len(B) == 1, 'cutoff-3 space is not one-dimensional')
        vec = [x / N[0][0].sqrt() for x in B[0]]
        idx = indices(parity, 3)
        ratios = []
        for s in samples:
            g = arb(s)
            product = arb(1)
            for a in (1, 2, 3):
                w = 2 * pi * a / state.L
                product *= g * g - w * w
            value = q_value(parity, vec, idx, state.L, g) * product / (g * g + arb(1) / 4)
            ratios.append(value * g if parity == 'even' else value)
        spread = max(abs(r - ratios[0]).upper() for r in ratios[1:])
        check(all(r.overlaps(ratios[0]) for r in ratios[1:]), 'closed form fails')
        out[parity] = {'constant_abs': BC.exact(abs(ratios[0]), 24), 'spread_upper': spread.str(3, radius=False)}
    return out


def verify_row(row: dict, zeros: list[str], tolerance: Fraction) -> None:
    """Recompute one comparison row and require agreement with the stored numbers and with the zero side."""
    fresh = compare_state(Fraction(row['L']), row['K'], row['bits'], zeros[:row['zeros_used']])
    tol = arb(tolerance.numerator) / tolerance.denominator
    for parity in ('even', 'odd'):
        stored, new = arb(row[parity]['prime_side']), arb(fresh[parity]['prime_side'])
        check(bool(abs(stored - new) < abs(new) / 10 ** 20), 'prime side differs from the stored value')
        zero = arb(fresh[parity]['zero_side'])
        check(bool(abs(new - zero) < abs(new) * tol), 'prime side and zero side disagree')
        check(bool(arb(row[parity]['relative_difference_upper']) < tol), 'stored relative difference exceeds the tolerance')


def main(argv: list[str]) -> int:
    zeros_path, K, bits, out = Path(argv[1]), int(argv[2]), int(argv[3]), Path(argv[4])
    zeros = json.loads(zeros_path.read_bytes())['gamma']
    rows = []
    for text in argv[5:]:
        row = compare_state(Fraction(text), K, bits, zeros)
        rows.append(row)
        print(f"L={text:>5} K={K} even {row['even']['prime_side'][:22]} (rel {row['even']['relative_difference_upper']})"
              f"  odd {row['odd']['prime_side'][:22]} (rel {row['odd']['relative_difference_upper']})", flush=True)
    record = {'schema': SCHEMA, 'RH': 'OPEN', 'Step4': 'OPEN', 'tool_sha256': BC.sha256(Path(__file__)),
              'native_source_sha256': BC.sha256(HERE / 'native_source.py'), 'zeros_sha256': BC.sha256(zeros_path),
              'claim': 'CONSISTENCY_CHECK_OF_A_LEAN_PROVED_IDENTITY_WITH_NUMERICAL_ZERO_INPUT_NOT_A_CERTIFICATE',
              'rows': rows}
    out.write_bytes((json.dumps(record, indent=1) + '\n').encode())
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
