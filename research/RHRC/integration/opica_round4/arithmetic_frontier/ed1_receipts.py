"""Witness-retaining successor of the frozen E-D1 tool (Increment 3F).

The frozen ``ed1_response.py`` (hash-bound by the E-H7 predeclaration) keeps
only the status and floating minimum of each ladder row. This tool runs the
same pencils, families and ladders and retains a receipt for every decision:

* CERTIFIED rows: the shift tau, the certified residual bound, the certified
  lower eigenvalue and the enclosure hash of the exact factor proposal R
  (A - tau I - R R^T = E with ||E||_F < tau; Lean consumer
  ``FiniteCertificateSoundness.posDef_of_shifted_factor``);
* FALSIFIED_BOUND rows: the exact dyadic witness vector (hex floats) and the
  enclosure of its quadratic value, so a verifier can recompute the negative
  value without trusting the status.

It does not replace or rescore E-D1 or E-H7; it re-derives their statuses with
receipts and records whether every status agrees with the frozen records. RH
and Step 4 remain OPEN.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('_frontier_ed1_for_receipts', HERE / 'ed1_response.py')
ED1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ED1)
NS = ED1.NS
K = NS.K
LADDER = ED1.LADDER
SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_ED1_RECEIPTS_V1'


def hexvec(v: np.ndarray) -> list[str]:
    return [float(x).hex() for x in np.asarray(v, dtype=float).ravel()]


def form_receipt(S, label: str) -> dict:
    """Kernel decision on S >= 0 with a retained receipt (same decision rule as native_slice.form_status)."""
    Sf = NS.sym(NS.to_float(S))
    ev, vec = np.linalg.eigh(Sf)
    out = {'statement': label, 'floating_minimum': float(ev[0])}
    if ev[0] > 0:
        tau = NS.dyadic_below(ev[0] / 2)
        R = NS.float_factor(Sf, tau)
        if R is None:
            out.update({'status': 'UNKNOWN_PRECISION', 'reason': 'floating shifted factorization failed', 'tau': str(tau)})
            return out
        cert = K.certify_shifted(S, tau, R)
        out.update(cert)
        out['receipt'] = {'kind': 'SHIFTED_FACTOR', 'tau': K.exact_str(tau), 'factor_enclosure_sha256': K.enclosure_sha256(R),
                          'factor_dimension': R.nrows(),
                          'lean_consumer': 'Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.posDef_of_shifted_factor'}
        return out
    v = vec[:, 0]
    val = K.quadratic(S, NS.exact_col(v))
    out.update({'status': 'FALSIFIED_BOUND' if K.certainly_negative(val) else 'UNKNOWN_PRECISION',
                'witness_value': K.ball_record(val), 'witness_kind': 'EXACT_DYADIC_FLOATING_EIGENVECTOR'})
    out['receipt'] = {'kind': 'EXACT_WITNESS', 'vector_hex': hexvec(v), 'vector_sha256': NS.array_sha256(v),
                      'lean_consumer': 'Zeta23.OPICARound4.ArithmeticFrontier.FiniteCertificateSoundness.not_nonneg_of_negative_witness'}
    return out


def run(L: Fraction, parity: str, eps: Fraction, split: int, bits: int = 192, ladder=LADDER, tail_max: int = 128) -> dict:
    t0 = time.time()
    st, B, k, recipe = ED1.pencil(L, parity, eps, split, bits)
    D, C, A = NS.blocks(B, k)
    Df, Cf, Af = NS.sym(NS.to_float(D)), NS.to_float(C), NS.sym(NS.to_float(A))
    lam, U = np.linalg.eigh(Af)
    a = NS.rational_below(0.98 * lam[0], 10 ** 6)
    b = NS.rational_above(1.02 * lam[-1], 1000)
    pre = NS.bound_test(A, a, 'lower')
    cap = NS.bound_test(A, b, 'upper')
    out = {'schema': SCHEMA, **NS.CAPS, 'L': str(st.Lq), 'K': st.K, 'parity': parity, 'tolerance': str(eps), 'split': split,
           'low_dimension': k, 'high_dimension': A.nrows(), 'bits': bits, 'a': str(a), 'b': str(b),
           'A_ge_aI': pre['status'], 'A_le_bI': cap['status'], 'A_ge_aI_record': pre, 'A_le_bI_record': cap,
           'hashes': {'tool_sha256': NS.SRC.sha256(Path(__file__)), 'ed1_sha256': NS.SRC.sha256(HERE / 'ed1_response.py'),
                      'engine_sha256': NS.SRC.sha256(HERE / 'native_slice.py'), 'source_module_sha256': NS.SRC.sha256(HERE / 'native_source.py'),
                      'kernel_sha256': NS.SRC.sha256(HERE / 'certificates.py'), 'backend_sha256': NS.SRC.sha256(NS.SRC.BACKEND_PATH)}}
    Xs = np.linalg.solve(Af, Cf.T)
    out['SCHUR_FULL_INVERSE_ACTION'] = {'family': 'INVERSE_RESIDUAL', 'proposal': 'X = A^-1 C^T (floating solve)',
                                        'X_proposal_sha256': NS.array_sha256(Xs),
                                        **form_receipt(K.inverse_residual_form(B, k, a, NS.exact(Xs)), 'S_X >= 0 with X = A^-1 C^T')}
    rho_vec = NS.exact_col(U[:, 0])
    rho_hi = float(K.upper(K.rayleigh(A, rho_vec)))
    vs = np.linalg.eigh(Df - Cf @ Cf.T / rho_hi)[1][:, 0]
    sg = K.refute_scalar_gap_for_all(B, k, rho_vec, NS.exact_col(vs))
    sg['receipt'] = {'kind': 'SCALAR_GAP_FOR_ALL_A', 'high_vector_hex': hexvec(U[:, 0]), 'low_vector_hex': hexvec(vs)}
    out['SCALAR_GAP'] = sg
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
            r = form_receipt(K.inverse_residual_form(B, k, a, NS.exact(Xf)), 'S_X >= 0, X = P_m(A) C^T proposal')
            r['X_proposal_sha256'] = NS.array_sha256(Xf)
        else:
            r = {'status': 'NOT_ELIGIBLE'}
        inv.append({'degree': m, **r})
        if m <= tail_max:
            if pre['status'] == 'CERTIFIED' and cap['status'] == 'CERTIFIED':
                Pm = Pa * (1 / K.q(b))
                S_tail = D - C * Pm * C.transpose() - C * C.transpose() * K.q((1 - a / b) ** m / a)
                rt = form_receipt(S_tail, 'S_tail >= 0')
            else:
                rt = {'status': 'NOT_ELIGIBLE'}
            tail.append({'degree': m, 'q_power_over_a': float((1 - a / b) ** m / a), **rt})

    def smallest(rows):
        ok = [r['degree'] for r in rows if r['status'] == 'CERTIFIED']
        return {'smallest_successful_tested_degree': min(ok) if ok else None, 'monotonicity': 'not assumed; every listed degree was tested'}
    out['INVERSE_RESIDUAL_LADDER'] = {'rows': inv, **smallest(inv)}
    out['GEOMETRIC_TAIL_LADDER'] = {'rows': tail, **smallest(tail), 'tested_up_to': tail_max}
    out['seconds'] = round(time.time() - t0, 1)
    return out


STATES = dict(ED1.STATES)
STATES.update({'L7_even_fifth': (Fraction(7), 'even', Fraction(1, 5), 1200), 'L7_odd_fifth': (Fraction(7), 'odd', Fraction(1, 5), 1200)})
TAIL_MAX = {'L7_even_fifth': 64, 'L7_odd_fifth': 64}


def compare(rec: dict, frozen: dict) -> dict:
    """Agreement of every status with the frozen E-D1/E-H7 record of the same state."""
    pairs = [('SCHUR_FULL_INVERSE_ACTION', rec['SCHUR_FULL_INVERSE_ACTION']['status'], frozen['SCHUR_FULL_INVERSE_ACTION']['status']),
             ('SCALAR_GAP', rec['SCALAR_GAP']['status'], frozen['SCALAR_GAP']['status'])]
    for fam in ('INVERSE_RESIDUAL_LADDER', 'GEOMETRIC_TAIL_LADDER'):
        fr = {r['degree']: r['status'] for r in frozen[fam]['rows']}
        for r in rec[fam]['rows']:
            pairs.append(('%s/%d' % (fam, r['degree']), r['status'], fr.get(r['degree'])))
    return {'agree': all(x == y for _, x, y in pairs), 'mismatches': [p for p in pairs if p[1] != p[2]], 'compared': len(pairs)}


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--states', required=True)
    p.add_argument('--out-dir', type=Path, required=True)
    a = p.parse_args(argv)
    a.out_dir.mkdir(parents=True, exist_ok=True)
    for name in a.states.split(','):
        L, par, eps, split = STATES[name]
        rec = run(L, par, eps, split, tail_max=TAIL_MAX.get(name, 128))
        rec['state_id'] = name
        frozen_file = (HERE / 'evidence' / ('increment3e' if name.startswith('L7') else 'increment3b') / ('ed1_%s.json' % name))
        if frozen_file.is_file():
            rec['agreement_with_frozen_record'] = {'file': str(frozen_file.relative_to(HERE)), 'sha256': hashlib.sha256(frozen_file.read_bytes()).hexdigest(),
                                                   **compare(rec, json.loads(frozen_file.read_bytes()))}
        (a.out_dir / ('receipts_%s.json' % name)).write_text(json.dumps(rec, indent=1) + '\n', encoding='utf-8')
        print(json.dumps({'state': name, 'inverse_residual': rec['INVERSE_RESIDUAL_LADDER']['smallest_successful_tested_degree'],
                          'agree': rec.get('agreement_with_frozen_record', {}).get('agree'),
                          'mismatches': rec.get('agreement_with_frozen_record', {}).get('mismatches'), 'seconds': rec['seconds']}), flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
