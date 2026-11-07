"""E-D1: coupled-response comparison on the native shifted pencils (Increment 3B).

On one pencil B = F + eps G of an actual moment slice, split on the Fourier
prefix flag into B = [[D, C], [C^T, A]] (corrected coordinates), this tool:

* runs the three certificate families of ``certificates.py`` (SCALAR_GAP,
  GEOMETRIC_TAIL, INVERSE_RESIDUAL) over a ladder of tested degrees and records
  the smallest successful *tested* degree of each (lesser degrees are tested,
  not inferred);
* certifies the exact Schur form with the full inverse action X = A^-1 C^T
  (floating proposal, kernel-certified residual form);
* decomposes the matrix response C A^-1 C^T = sum_k (C u_k)(C u_k)^T / lambda_k
  by spectral band of A, with the cumulative coupling mass
  M(s) = C 1_(0,s](A) C^T, and compares each partial response with D in
  Loewner terms (lambda_min of D minus that response).

Spectral bands use floating eigenvectors of A: they are EXPERIMENTAL SIGNALS,
not certified projectors. Every CERTIFIED/FALSIFIED status comes from the
kernel. RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('_frontier_native_slice_ed1', HERE / 'native_slice.py')
NS = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(NS)
K = NS.K
LADDER = (1, 2, 4, 8, 16, 32, 64, 128, 256)


def pencil(L: Fraction, parity: str, eps: Fraction, split: int, bits: int):
    st = NS.SRC.NativeState(L, bits=bits)
    K.validate_state(st.Lq, st.K, st.Q, [q for q, _ in st.atoms])
    M, w = st.reduced(parity)
    C = st.constraints(parity)
    split_idx = split + 1 if parity == 'even' else split
    Zf, nlow = NS.flag_basis(NS.to_float(C), w, split_idx)
    Y, recipe = NS.corrected(Zf, C, [(0, nlow, split_idx), (nlow, Zf.shape[1], len(w))])
    W = NS.arb_mat([[NS.arb(w[i]) if i == j else NS.arb(0) for j in range(len(w))] for i in range(len(w))])
    F = Y.transpose() * M * Y
    G = Y.transpose() * W * Y
    return st, F + K.q(eps) * G, nlow, recipe


def run(L: Fraction, parity: str, eps: Fraction, split: int, bits: int = 192, ladder=LADDER, tail_max: int = 128) -> dict:
    t0 = time.time()
    st, B, k, recipe = pencil(L, parity, eps, split, bits)
    D, C, A = NS.blocks(B, k)
    Df, Cf, Af = NS.sym(NS.to_float(D)), NS.to_float(C), NS.sym(NS.to_float(A))
    lam, U = np.linalg.eigh(Af)
    a = NS.rational_below(0.98 * lam[0], 10 ** 6)
    b = NS.rational_above(1.02 * lam[-1], 1000)
    pre = NS.bound_test(A, a, 'lower')
    cap = NS.bound_test(A, b, 'upper')
    out = {'schema': 'OPICA4_ARITHMETIC_FRONTIER_ED1_V1', **NS.CAPS, 'L': str(st.Lq), 'K': st.K, 'parity': parity,
           'tolerance': str(eps), 'split': split, 'low_dimension': k, 'high_dimension': A.nrows(), 'bits': bits,
           'coordinates': 'corrected Fourier-prefix flag (orthonormal proposal; the pencil carries the full Gram)',
           'a': str(a), 'b': str(b), 'A_ge_aI': pre['status'], 'A_le_bI': cap['status'],
           'engine_sha256': NS.SRC.sha256(HERE / 'native_slice.py'), 'tool_sha256': NS.SRC.sha256(Path(__file__)),
           'kernel_sha256': NS.SRC.sha256(HERE / 'certificates.py')}
    # exact Schur form with the full inverse action
    Xs = np.linalg.solve(Af, Cf.T)
    S_full = K.inverse_residual_form(B, k, a, NS.exact(Xs))
    out['SCHUR_FULL_INVERSE_ACTION'] = {'family': 'INVERSE_RESIDUAL', 'proposal': 'X = A^-1 C^T (floating solve)',
                                        **NS.form_status(S_full, 'S_X >= 0 with X = A^-1 C^T')}
    # scalar gap
    rho_vec = NS.exact_col(U[:, 0])
    rho_hi = float(K.upper(K.rayleigh(A, rho_vec)))
    vs = np.linalg.eigh(Df - Cf @ Cf.T / rho_hi)[1][:, 0]
    out['SCALAR_GAP'] = K.refute_scalar_gap_for_all(B, k, rho_vec, NS.exact_col(vs))
    # degree ladders
    inv, tail = [], []
    Tf = np.eye(A.nrows()) - Af / float(b)
    P, term, done = np.zeros_like(Af), np.eye(A.nrows()), 0
    Pa, terma = K.identity(A.nrows(), 0), K.identity(A.nrows())
    Ta = K.identity(A.nrows()) - A * (1 / K.q(b))
    for m in ladder:
        while done < m:
            P += term
            term = term @ Tf
            if m <= tail_max:
                Pa = Pa + terma
                terma = terma * Ta
            done += 1
        Xf = (P / float(b)) @ Cf.T
        if pre['status'] == 'CERTIFIED':
            st_inv = NS.form_status(K.inverse_residual_form(B, k, a, NS.exact(Xf)), 'S_X >= 0, X = P_m(A) C^T proposal')
        else:
            st_inv = {'status': 'NOT_ELIGIBLE'}
        inv.append({'degree': m, 'status': st_inv['status'], 'floating_minimum': st_inv.get('floating_minimum')})
        if m <= tail_max:
            if pre['status'] == 'CERTIFIED' and cap['status'] == 'CERTIFIED':
                Pm = Pa * (1 / K.q(b))
                S_tail = D - C * Pm * C.transpose() - C * C.transpose() * K.q((1 - a / b) ** m / a)
                st_tail = NS.form_status(S_tail, 'S_tail >= 0')
            else:
                st_tail = {'status': 'NOT_ELIGIBLE'}
            tail.append({'degree': m, 'status': st_tail['status'], 'q_power_over_a': float((1 - a / b) ** m / a),
                         'floating_minimum': st_tail.get('floating_minimum')})
    def smallest(rows):
        ok = [r['degree'] for r in rows if r['status'] == 'CERTIFIED']
        return {'smallest_successful_tested_degree': min(ok) if ok else None,
                'all_tested_degrees_below_it_failed_or_unresolved': True if ok else None,
                'monotonicity': 'not assumed; every listed degree was tested'}
    out['INVERSE_RESIDUAL_LADDER'] = {'rows': inv, **smallest(inv)}
    out['GEOMETRIC_TAIL_LADDER'] = {'rows': tail, **smallest(tail), 'tested_up_to': tail_max}
    # matrix response by band (EXPERIMENTAL)
    CU = Cf @ U
    contrib = CU ** 2  # (low_dim, high_dim) squared couplings per eigenvector
    bands = [float(eps) + d for d in (1e-12, 1e-9, 1e-6, 1e-3)] + [2 * float(eps), 4 * float(eps), 1.0, float(lam[-1]) + 1]
    resp_full = (CU / lam) @ CU.T
    schur_min = float(np.linalg.eigvalsh(Df - resp_full)[0])
    rows = []
    for s in bands:
        sel = lam <= s
        Ms = CU[:, sel] @ CU[:, sel].T
        R_low = (CU[:, sel] / lam[sel]) @ CU[:, sel].T
        R_high = resp_full - R_low
        rows.append({'s': s, 'count': int(sel.sum()), 'trace_M_s': float(np.trace(Ms)),
                     'max_eig_M_s': float(np.linalg.eigvalsh(Ms)[-1]) if sel.any() else 0.0,
                     'trace_low_response': float(np.trace(R_low)),
                     'max_eig_low_response': float(np.linalg.eigvalsh(R_low)[-1]) if sel.any() else 0.0,
                     'min_eig_D_minus_high_response': float(np.linalg.eigvalsh(Df - R_high)[0])})
    near = lam <= float(eps) + 1e-6
    out['RESPONSE_BANDS'] = {
        'authority': 'EXPERIMENTAL_SIGNAL_FLOATING_SPECTRAL_PROJECTORS',
        'min_eig_D': float(np.linalg.eigvalsh(Df)[0]), 'min_eig_schur_D_minus_CAinvCT': schur_min,
        'trace_full_response': float(np.trace(resp_full)), 'max_eig_full_response': float(np.linalg.eigvalsh(resp_full)[-1]),
        'near_band': {'definition': 'eigenvalues of A within 1e-6 of eps (the shifted near-null directions)',
                      'count': int(near.sum()), 'trace_coupling_mass': float(contrib[:, near].sum()),
                      'max_column_coupling': float(np.sqrt(contrib[:, near].sum(axis=0)).max()) if near.any() else 0.0,
                      'response_trace': float((contrib[:, near] / lam[near]).sum()) if near.any() else 0.0,
                      'scalar_gap_worst_charge': float(np.linalg.eigvalsh(Cf @ Cf.T)[-1] / lam[0])},
        'bands': rows}
    out['seconds'] = round(time.time() - t0, 1)
    return out


STATES = {
    'L4_even_half': (Fraction(4), 'even', Fraction(1, 2), 128), 'L4_odd_half': (Fraction(4), 'odd', Fraction(1, 2), 128),
    'L4_even_1024': (Fraction(4), 'even', Fraction(1, 1024), 128),
    'L5_even_third': (Fraction(5), 'even', Fraction(1, 3), 312), 'L5_odd_third': (Fraction(5), 'odd', Fraction(1, 3), 312),
    'L6_even_quarter': (Fraction(6), 'even', Fraction(1, 4), 648), 'L6_odd_quarter': (Fraction(6), 'odd', Fraction(1, 4), 648),
}


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--states', required=True)
    p.add_argument('--out-dir', type=Path, required=True)
    p.add_argument('--tail-max', type=int, default=128)
    a = p.parse_args(argv)
    a.out_dir.mkdir(parents=True, exist_ok=True)
    for name in (list(STATES) if a.states == 'all' else a.states.split(',')):
        L, par, eps, split = STATES[name]
        rec = run(L, par, eps, split, tail_max=a.tail_max)
        rec['state_id'] = name
        (a.out_dir / ('ed1_%s.json' % name)).write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
        print(json.dumps({'state': name, 'inverse_residual': rec['INVERSE_RESIDUAL_LADDER']['smallest_successful_tested_degree'],
                          'tail': rec['GEOMETRIC_TAIL_LADDER']['smallest_successful_tested_degree'],
                          'schur': rec['SCHUR_FULL_INVERSE_ACTION']['status'], 'seconds': rec['seconds']}), flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
