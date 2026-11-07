"""Threshold scan of the near-null statistics on the native moment slices (version 2).

Records, per threshold 10^-t, the absolute count #{|lambda| < 10^-t}, the signed
count #{lambda < 10^-t} and the floating negative count, with N_main(T), the
main terms of the Riemann-von Mangoldt count at T = 2 pi K / L. Version 1 (which
counted only lambda < delta) is preserved in evidence/increment2/producer/.

EXPERIMENTAL SIGNAL only: floating eigenvalues are not certificates and
N_main(T) is not a certified zero count. RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('_frontier_native_slice_scan', HERE / 'native_slice.py')
NS = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(NS)


def scan(L: Fraction, parity: str, bits: int = 128) -> dict:
    st = NS.SRC.NativeState(L, bits=bits)
    M, w = st.reduced(parity)
    C = st.constraints(parity)
    Zf = NS.kernel_basis(NS.to_float(C), w, len(w))
    Mf = NS.to_float(M)
    Wf = NS.np.diag(NS.np.array(w, dtype=float))
    ev, _ = NS.generalized_eig(Zf.T @ Mf @ Zf, Zf.T @ Wf @ Zf)
    return {'L': str(L), 'K': st.K, 'parity': parity, 'dimension': Zf.shape[1],
            **NS.spectral_stats(ev, Zf.shape[1], st.K, Fraction(L))}


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--L', action='append', required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(argv)
    rows = [scan(Fraction(L), parity) for L in a.L for parity in ('even', 'odd')]
    rec = {'schema': 'OPICA4_ARITHMETIC_FRONTIER_NULLCOUNT_SCAN_V2', 'RH': 'OPEN', 'Step4': 'OPEN',
           'authority': 'EXPERIMENTAL_SIGNAL_FLOATING_ONLY', 'rows': rows,
           'engine_sha256': NS.SRC.sha256(HERE / 'native_slice.py'), 'scan_sha256': NS.SRC.sha256(Path(__file__))}
    a.out.write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
