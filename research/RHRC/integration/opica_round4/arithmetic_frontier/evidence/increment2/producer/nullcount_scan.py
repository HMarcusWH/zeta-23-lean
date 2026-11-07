"""Threshold scan of the near-null count on the native moment slices.

For each state the floating generalized spectrum of the slice form (physical
metric) is counted below the thresholds 10^-t, t = 2, 4, ..., 13, and compared
with dim - N(T), where T = 2 pi K / L and N(T) is the main term
(T/2pi) log(T/2pi) - T/2pi + 7/8 of the Riemann-von Mangoldt count.

EXPERIMENTAL SIGNAL only: floating eigenvalues are not certificates, and the
comparison uses main terms, not the zero count itself. RH and Step 4 remain
OPEN.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('_frontier_native_slice_scan', HERE / 'native_slice.py')
NS = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(NS)
THRESHOLDS = (2, 4, 6, 8, 10, 12, 13)


def main_term(T: float) -> float:
    t = T / (2 * math.pi)
    return t * math.log(t) - t + 7 / 8


def scan(L: Fraction, parity: str, bits: int = 128) -> dict:
    st = NS.NativeState(L, bits=bits)
    M, w = st.reduced(parity)
    Z = NS.kernel_basis(NS.to_float(st.constraints(parity)), w, len(w))
    Mf = NS.to_float(M)
    F = Z.T @ Mf @ Z
    G = Z.T @ (np.array(w, dtype=float)[:, None] * Z)
    Li = np.linalg.inv(np.linalg.cholesky((G + G.T) / 2))
    ev = np.linalg.eigvalsh(Li @ ((F + F.T) / 2) @ Li.T)
    dim = Z.shape[1]
    T = 2 * math.pi * st.K / float(L)
    return {'L': str(L), 'K': st.K, 'Q': st.Q, 'parity': parity, 'dimension': dim, 'T': T,
            'dim_minus_main_term_N_T': dim - main_term(T),
            'counts_below_10^-t': {str(t): int(np.sum(ev < 10.0 ** -t)) for t in THRESHOLDS},
            'count_between_1e-2_and_1': int(np.sum((ev >= 1e-2) & (ev < 1))),
            'smallest_eigenvalue_above_1e-2': float(ev[ev >= 1e-2][0])}


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--L', action='append', required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(argv)
    rows = [scan(Fraction(L), parity) for L in a.L for parity in ('even', 'odd')]
    rec = {'schema': 'OPICA4_ARITHMETIC_FRONTIER_NULLCOUNT_SCAN_V1', 'RH': 'OPEN', 'Step4': 'OPEN',
           'authority': 'EXPERIMENTAL_SIGNAL_FLOATING_ONLY',
           'engine_sha256': hashlib.sha256((HERE / 'native_slice.py').read_bytes()).hexdigest(),
           'scan_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'rows': rows,
           'timing_note': 'Scan run after the L=6 records were read; this is a post-hoc robustness check of P8, not a prediction.'}
    a.out.write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
