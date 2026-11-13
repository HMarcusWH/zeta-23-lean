"""Least-crossing selector in a HYPOTHETICAL-zero model (ball arithmetic; not the zeta function).

Model form on the native pole-neutral boundary-flat parity spaces at cutoff ``K``:

    E_model = E_on + E_off,
    E_on (x) = (8/L)  * sum_{gamma > 0} sin^2(gamma L/2) q_x(gamma)^2      (stored numerical zero ordinates)
    E_off(x) = (16/L) * Re[ sinh^2(p L/2) R_x(p)^2 ],  p = delta + i gamma0  (one ADDED off-line quadruple)

    even: R(z) = x_0/z + sum_a 2 x_a z/(z^2 + w_a^2),    odd: R(z) = sum_a 2 i x_a w_a/(z^2 + w_a^2),  w_a = 2 pi a / L.

``E_on`` is the explicit-formula value of the canonical form if the retained
on-line zeros were all the zeros; ``E_off`` is what one extra quadruple
``{+-p, +-conj p}`` would add. The selector rule is the one of
``Zeta23/CCM/NativeDeepThresholdGround.lean``: the least ``K >= 3`` whose global
bottom is below ``-eta``, for ``D/3 < eta < D/2`` and ``D = exp(beta L)``. The
tool decides ``bottom < -eta`` by certified inertia of ``G + eta N`` and reports
the selected cutoff for the two extreme thresholds ``eta = D/2`` and ``eta = D/3``.

This is a model computation. It shows what the selector would do IF such a zero
existed; it has no Euler product and says nothing about whether one exists.
EXPERIMENTAL SIGNAL / illustration of a paper derivation. RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_SELECTOR_MODEL_V1'


def _load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BC = _load('_frontier_bottom_certificate_selector', 'bottom_certificate.py')
SL = _load('_frontier_spectral_lowdeg_selector', 'spectral_lowdeg.py')


class ModelFailure(ArithmeticError):
    """A stored model row does not reproduce."""


def check(value: bool, message: str) -> None:
    if not value:
        raise ModelFailure(message)


def rational(q) -> arb:
    q = Fraction(q)
    return arb(q.numerator) / q.denominator


def constraint_rows(parity: str, K: int, L: arb) -> list[list[arb]]:
    """Boundary-flat and pole rows in the reduced coordinates of ``native_source.constraints``."""
    pi = arb.pi()
    if parity == 'even':
        w = [arb(1) if a == 0 else arb(2) for a in range(K + 1)]
        return [[w[a] for a in range(K + 1)], [w[a] * a * a for a in range(K + 1)],
                [w[a] * L / (L ** 2 + 16 * pi ** 2 * a * a) for a in range(K + 1)]]
    return [[arb(2 * a) for a in range(1, K + 1)],
            [8 * pi * a / (L ** 2 + 16 * pi ** 2 * a * a) for a in range(1, K + 1)]]


def basis(parity: str, K: int, L: arb):
    rows = constraint_rows(parity, K, L)
    n = len(rows[0])
    r = len(rows)

    class _C:
        def __getitem__(self, key):
            return rows[key[0]][key[1]]
    B = BC.null_basis(_C(), list(range(r)), n)
    weights = [1 if (parity == 'even' and i == 0) else 2 for i in range(n)]
    return B, weights


def off_value(parity: str, vec: list[arb], idx: list[int], L: arb, p: acb) -> acb:
    pi = arb.pi()
    if parity == 'even':
        total = acb(vec[0]) / p
        for x, a in zip(vec[1:], idx[1:]):
            w = 2 * pi * a / L
            total += 2 * x * p / (p * p + w * w)
        return total
    total = acb(0)
    for x, a in zip(vec, idx):
        w = 2 * pi * a / L
        total += acb(0, 1) * (2 * x * w) / (p * p + w * w)
    return total


def model_pencil(parity: str, K: int, L: arb, zeros: list[arb], p: acb):
    B, weights = basis(parity, K, L)
    d = len(B)
    if d == 0:
        return [], []
    n = len(weights)
    idx = SL.indices(parity, K)
    N = [[sum((arb(weights[a]) * B[i][a] * B[j][a] for a in range(n)), arb(0)) for j in range(d)] for i in range(d)]
    G = SL.zero_gram(parity, B, K, L, zeros)
    half = (p * L / 2).exp()
    sinh2 = ((half - 1 / half) / 2) ** 2
    Rp = [off_value(parity, v, idx, L, p) for v in B]
    for i in range(d):
        for j in range(d):
            G[i][j] = G[i][j] + 16 / L * (sinh2 * Rp[i] * Rp[j]).real
    return G, N


def crosses(K: int, L: arb, zeros: list[arb], p: acb, eta: arb) -> bool:
    """Certified: the global model bottom at cutoff ``K`` is below ``-eta``."""
    for parity in ('even', 'odd'):
        G, N = model_pencil(parity, K, L, zeros, p)
        if G and BC.count_below(G, N, -eta) >= 1:
            return True
    return False


def selected_cutoff(L: arb, zeros: list[arb], p: acb, eta: arb, k_max: int) -> int | None:
    for K in range(3, k_max + 1):
        if crosses(K, L, zeros, p, eta):
            return K
    return None


def model_row(L, delta, gamma0, beta, k_max: int, bits: int, zeros: list[str]) -> dict:
    ctx.prec = bits
    Lb, gam = rational(L), [arb(s) for s in zeros]
    p = acb(rational(delta), rational(gamma0))
    D = (rational(beta) * Lb).exp()
    row = {'L': str(Fraction(L)), 'cos_gamma0_L': (rational(gamma0) * Lb).cos().str(6, radius=False)}
    for label, eta in (('eta_D_over_2', D / 2), ('eta_D_over_3', D / 3)):
        row['selected_cutoff_' + label] = selected_cutoff(Lb, gam, p, eta, k_max)
    bottoms = {}
    for K in (3, 4):
        values = []
        for parity in ('even', 'odd'):
            G, N = model_pencil(parity, K, Lb, gam, p)
            values.append(SL.pencil_bottom(G, N))
        bottoms[str(K)] = BC.exact(min(values, key=lambda v: v.mid()), 12)
    row['model_bottom'] = bottoms
    row['minus_D_over_2'] = BC.exact(-D / 2, 12)
    return row


def verify_row(row: dict, params: dict, zeros: list[str]) -> None:
    fresh = model_row(Fraction(row['L']), params['delta'], params['gamma0'], params['beta'], params['k_max'],
                      params['bits'], zeros[:params['zeros_used']])
    for key in ('selected_cutoff_eta_D_over_2', 'selected_cutoff_eta_D_over_3'):
        check(fresh[key] == row[key], 'selected cutoff differs from the stored row')


def main(argv: list[str]) -> int:
    zeros_path, out = Path(argv[1]), Path(argv[2])
    delta, gamma0, beta = Fraction(argv[3]), Fraction(argv[4]), Fraction(argv[5])
    k_max, bits = int(argv[6]), int(argv[7])
    start, stop, step = Fraction(argv[8]), Fraction(argv[9]), Fraction(argv[10])
    zeros = json.loads(zeros_path.read_bytes())['gamma']
    rows = []
    L = start
    while L <= stop:
        row = model_row(L, delta, gamma0, beta, k_max, bits, zeros)
        rows.append(row)
        print(f"L={row['L']:>10} cos={row['cos_gamma0_L']:>10} K(D/2)={row['selected_cutoff_eta_D_over_2']} "
              f"K(D/3)={row['selected_cutoff_eta_D_over_3']} bottom3={row['model_bottom']['3']} bottom4={row['model_bottom']['4']}",
              flush=True)
        L += step
    record = {'schema': SCHEMA, 'RH': 'OPEN', 'Step4': 'OPEN', 'tool_sha256': BC.sha256(Path(__file__)),
              'zeros_sha256': BC.sha256(zeros_path),
              'claim': 'MODEL_WITH_ONE_ADDED_OFF_LINE_QUADRUPLE_NOT_THE_ZETA_FUNCTION_NO_EULER_PRODUCT',
              'parameters': {'delta': str(delta), 'gamma0': str(gamma0), 'beta': str(beta), 'k_max': k_max, 'bits': bits,
                             'zeros_used': len(zeros)},
              'rows': rows}
    out.write_bytes((json.dumps(record, indent=1) + '\n').encode())
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
