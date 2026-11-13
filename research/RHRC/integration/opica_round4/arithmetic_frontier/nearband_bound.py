"""Certified projector-free near-band coupling bounds (Increment 3C).

Native object. For the shifted pencil B = F + eps G of an actual moment slice
in the corrected Fourier-prefix flag coordinates of E-D1, write
B = [[D, C], [C^T, A]]. The near-band coupling mass at spectral cutoff s is

    M(s) = C 1_(-inf,s](A) C^T          (coordinate statement, as in E-D1).

DERIVED bound. For b > s and k >= 0 the even power
phi_k(lam) = ((b - lam)/(b - s))^(2^k) satisfies phi_k >= 1_(-inf,s] on the
whole real line (for lam <= s the base is >= 1; an even power is >= 0). Hence,
for the same exact symmetric A,

    M(s) <= C Phi_k C^T,     Phi_k = ((b I - A)/(b - s))^(2^k),

and when A >= a I > 0 is certified, also
C A^-1 1_(0,s](A) C^T <= C A^-1 Phi_k C^T. No eigenvector, projector or gap is
assumed: the right-hand sides are computed in Arb by k exact squarings of an
enclosure of the exact native A. A <= b I only decides how informative the
bound is (phi_k <= 1 on [s, 2b - s]). The bound is resolution-limited: an
eigenvalue x above s keeps weight about exp(-2^k x/(b - s)), recorded as
`resolution_1e-10`; the weight on [lambda_min, s] is at most
phi_k(lambda_min), recorded from the floating spectrum.

Synthetic controls (SYNTHETIC, not native objects). The question is whether
small near-band coupling discriminates positive from negative pencils.

* S1 subtracts a rank-one term on the first low-block coordinate. C and A are
  unchanged entrywise, so the near-band bound is identical while the pencil is
  certified negative. Small coupling therefore cannot be a sign criterion.
* S2 merges two adjacent actual zeros 1/2 + i gamma_n and 1/2 + i gamma_{n+1}
  and moves them off the line as one quartet 1/2 +- delta +- i gamma_mid, in
  the explicit-formula representation of the native form,
  Q = sum_rho Re conj(U(-conj w)) U(w) with w = rho - 1/2. The mode transform
  U_n(w) = (e^{wL} - 1) sqrt(L) / (wL + 2 pi i n) is calibrated on the native
  pole channel (at w = +-1/2 it reproduces the native pole matrix), and the
  truncated zero sum reproduces pole - arch - prime at a small state
  (EXPERIMENTAL; recorded). The perturbation
  N(delta) = quartet - pair(gamma_n) - pair(gamma_n+1) is unscaled; its
  floating detection threshold eps*(delta) = -lambda_min(F + N, G) is
  recorded for several delta. At delta = 1/10 the tool certifies the
  synthetic pencil at the checkpoint tolerance, positive (blind) or negative,
  and compares certified near-band bounds of the native and synthetic pencils
  at one common tolerance below eps*, where the native pencil is certified
  positive and the synthetic one certified negative.

Floating spectral projections are reported only for comparison and are
labelled EXPERIMENTAL. RH and Step 4 remain OPEN.
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

HERE = Path(__file__).resolve().parent


def _load(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


NS = _load('_frontier_native_slice_nb', 'native_slice.py')
K = NS.K
from flint import arb_mat, ctx  # noqa: E402

SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_NEARBAND_BOUND_V1'
OFFSETS = (Fraction(1, 10 ** 8), Fraction(1, 10 ** 6), Fraction(1, 10 ** 4), Fraction(1, 10 ** 2))


def dyadic_above(x: float) -> Fraction:
    if not x > 0:
        raise ValueError('positive value required')
    m, e = math.frexp(x)
    return Fraction(math.ceil(m * 2 ** 40) + 1, 2 ** 40) * (Fraction(2) ** e if e >= 0 else Fraction(1, 2 ** (-e)))


def native_pencil(L: Fraction, parity: str, eps: Fraction, split: int, bits: int) -> dict:
    """The E-D1 pencil (same construction as ed1_response.pencil), keeping F, G and the basis."""
    st = NS.SRC.NativeState(L, bits=bits)
    K.validate_state(st.Lq, st.K, st.Q, [q for q, _ in st.atoms])
    M, w = st.reduced(parity)
    C = st.constraints(parity)
    split_idx = split + 1 if parity == 'even' else split
    Zf, nlow = NS.flag_basis(NS.to_float(C), w, split_idx)
    Y, recipe = NS.corrected(Zf, C, [(0, nlow, split_idx), (nlow, Zf.shape[1], len(w))])
    W = arb_mat([[NS.arb(w[i]) if i == j else NS.arb(0) for j in range(len(w))] for i in range(len(w))])
    F = Y.transpose() * M * Y
    G = Y.transpose() * W * Y
    return {'state': st, 'Y': Y, 'F': F, 'G': G, 'B': F + K.q(eps) * G, 'k': nlow, 'weights': w}


def phi_power(A: arb_mat, b: Fraction, s: Fraction, k: int) -> arb_mat:
    T = (K.identity(A.nrows(), K.q(b)) - A) * (1 / K.q(b - s))
    for _ in range(k):
        T = T * T
    return T


def trace(M: arb_mat):
    t = M[0, 0]
    for i in range(1, M.nrows()):
        t = t + M[i, i]
    return t


def nearband_bounds(B: arb_mat, k_low: int, eps: Fraction, offsets=OFFSETS, response: bool = True) -> dict:
    D, C, A = NS.blocks(B, k_low)
    Af, Cf = NS.sym(NS.to_float(A)), NS.to_float(C)
    lam, U = np.linalg.eigh(Af)
    CU2 = (Cf @ U) ** 2
    col = CU2.sum(axis=0)
    b = NS.rational_above(1.02 * max(lam[-1], 1e-3), 1000)
    cap = NS.bound_test(A, b, 'upper')
    out = {'b': str(b), 'A_le_bI': cap['status'], 'floating_lambda_min_A': float(lam[0]),
           'floating_lambda_max_A': float(lam[-1]), 'rows': []}
    pre = None
    if lam[0] > 0:
        a = NS.rational_below(0.98 * lam[0], 10 ** 6)
        if a > 0:
            pre = NS.bound_test(A, a, 'lower')
            out['a'], out['A_ge_aI'] = str(a), pre['status']
    if pre is None:
        out['A_ge_aI'] = 'NOT_ELIGIBLE_FLOATING_LAMBDA_MIN_NONPOSITIVE'
    for off in offsets:
        s = eps + off
        width = max(float(s) - lam[0], 1e-30)
        k = max(0, min(24, int(math.floor(math.log2(max(1.0, 0.5 * (float(b) - float(s)) / width))))))
        Phi = phi_power(A, b, s, k)
        Mb = K.symmetrized(C * Phi * C.transpose())
        tr = trace(Mb)
        Mbf = NS.sym(NS.to_float(Mb))
        lmax = float(np.linalg.eigvalsh(Mbf)[-1])
        beta = dyadic_above(1.01 * max(lmax, 1e-300))
        lam_cert = NS.bound_test(Mb, beta, 'upper')
        res = (float(b) - float(s)) * 23.03 / (2 ** k)
        phi_f = ((float(b) - lam) / (float(b) - float(s))) ** (2 ** k)
        row = {'s': str(s), 'offset_above_eps': str(off), 'k': k, 'power': 2 ** k,
               'certified_trace_upper': K.float_str(K.upper(tr)),
               'trace_ball': K.ball_record(tr),
               'certified_lambda_max_upper': {'beta': K.exact_str(beta), 'beta_float': float(beta), 'status': lam_cert['status']},
               'statement': 'tr M(s) <= tr(C Phi_k C^T) and lambda_max M(s) <= beta (each CERTIFIED where stated; DERIVED pointwise majorant)',
               'resolution_1e-10': res,
               'weight_at_floating_lambda_min': float(phi_f[0]),
               'experimental_floating': {
                   'authority': 'EXPERIMENTAL_SIGNAL_FLOATING_SPECTRAL_PROJECTORS',
                   'count_at_or_below_s': int(np.sum(lam <= float(s))),
                   'trace_M_s': float(col[lam <= float(s)].sum()),
                   'trace_M_s_plus_resolution': float(col[lam <= float(s) + res].sum()),
                   'trace_C_phi_CT': float((col * phi_f).sum())}}
        if response and pre is not None and pre['status'] == 'CERTIFIED':
            R = C * A.solve(Phi * C.transpose())
            row['certified_response_trace_upper'] = K.float_str(K.upper(trace(R)))
            row['response_statement'] = 'tr(C A^-1 1_(0,s](A) C^T) <= tr(C A^-1 Phi_k C^T) (A >= aI > 0 certified)'
        out['rows'].append(row)
    CC = K.symmetrized(C * C.transpose())
    out['trace_CCT_upper'] = K.float_str(K.upper(trace(CC)))
    if lam[0] > 0:
        out['scalar_gap_charge_float'] = float(np.linalg.eigvalsh(NS.to_float(CC))[-1] / lam[0])
    return out


# ----------------------------------------------------------------------------- synthetic controls

def mode_transform(L: float, n: np.ndarray, w: complex) -> np.ndarray:
    """U_n(w) = int_0^L e^{(w + 2 pi i n/L) x} dx / sqrt(L), the convention calibrated on the pole channel."""
    return (np.exp(w * L) - 1) * math.sqrt(L) / (w * L + 2j * math.pi * n)


def reduced_transform(L: float, Kc: int, parity: str, w: complex) -> np.ndarray:
    j = np.arange(0, Kc + 1) if parity == 'even' else np.arange(1, Kc + 1)
    if parity == 'even':
        v = mode_transform(L, j, w) + mode_transform(L, -j, w)
        v[0] = mode_transform(L, np.array([0]), w)[0]
        return v
    return mode_transform(L, j, w) - mode_transform(L, -j, w)


def zero_form(L: float, Kc: int, parity: str, ws, basis: np.ndarray | None = None) -> np.ndarray:
    """sum_w Re conj(U(-conj w)) U(w)^T, symmetrized, in reduced (or basis) coordinates."""
    out = 0
    for w in ws:
        a1, a2 = reduced_transform(L, Kc, parity, -np.conj(w)), reduced_transform(L, Kc, parity, w)
        if basis is not None:
            a1, a2 = basis.T @ a1, basis.T @ a2
        X = np.outer(a1.real, a2.real) + np.outer(a1.imag, a2.imag)
        out = out + (X + X.T) / 2
    return out


def pole_calibration(bits: int = 128) -> dict:
    st = NS.SRC.NativeState(Fraction(2), K=16, bits=bits)
    rows = {}
    for parity in ('even', 'odd'):
        _, _, ch = st.reduced(parity, with_channels=True)
        P = NS.to_float(ch['pole'])
        Z = zero_form(2.0, 16, parity, (0.5, -0.5))
        rows[parity] = float(np.abs(P - Z).max() / np.abs(P).max())
    return {'state': 'L=2, K=16', 'relative_max_error': rows,
            'statement': 'sum over w = +-1/2 of the calibrated mode-transform form reproduces the native pole channel'}


def explicit_formula_check(n_zeros: int = 400, bits: int = 128) -> dict:
    """EXPERIMENTAL: the native form against the partial zero sum sum_{gamma <= T} Re conj(U(i gamma)) U(i gamma)."""
    import mpmath
    gam = [float(mpmath.zetazero(n).imag) for n in range(1, n_zeros + 1)]
    st = NS.SRC.NativeState(Fraction(2), K=16, bits=bits)
    rows = {}
    for parity in ('even', 'odd'):
        Mf = NS.to_float(st.reduced(parity)[0])
        part = lambda m: sum(zero_form(2.0, 16, parity, (complex(0, g), complex(0, -g))) for g in gam[:m])
        rows[parity] = {'max_abs_native': float(np.abs(Mf).max()),
                        'max_abs_error_all_zeros': float(np.abs(Mf - part(n_zeros)).max()),
                        'max_abs_error_half_zeros': float(np.abs(Mf - part(n_zeros // 2)).max())}
    return {'authority': 'EXPERIMENTAL_SIGNAL', 'state': 'L=2, K=16', 'zeros': n_zeros, 'largest_ordinate': gam[-1],
            'rows': rows, 'statement': 'pole - arch - prime agrees with the truncated zero sum in the calibrated convention; '
            'the error decreases as zeros are added (explicit-formula representation; tail not bounded)'}


def zero_pair_near(T: float) -> tuple[int, float, float]:
    import mpmath
    n = max(1, int(round(NS.main_term_N(T))))
    return n, float(mpmath.zetazero(n).imag), float(mpmath.zetazero(n + 1).imag)


def certify_or_witness(Bp: arb_mat, Gf: np.ndarray | None = None) -> dict:
    """CERTIFIED (Bp > 0) by a kernel certificate, or FALSIFIED_BOUND by an exact negative vector."""
    Bf = NS.sym(NS.to_float(Bp))
    ev, vec = np.linalg.eigh(Bf)
    if ev[0] > 0:
        return {'floating_minimum': float(ev[0]), **NS.certify(Bp, NS.dyadic_below(ev[0] / 2), Bf)}
    val = K.quadratic(Bp, NS.exact_col(vec[:, 0]))
    return {'floating_minimum': float(ev[0]), 'status': 'FALSIFIED_BOUND' if K.certainly_negative(val) else 'UNKNOWN_PRECISION',
            'witness_value': K.ball_record(val), 'witness_kind': 'EXACT_DYADIC_FLOATING_EIGENVECTOR'}


def nearband_summary(Bp: arb_mat, k_low: int, eps_t: Fraction) -> dict:
    nb = nearband_bounds(Bp, k_low, eps_t, offsets=(Fraction(1, 10 ** 6),), response=False)
    r = nb['rows'][0]
    return {'A_ge_aI': nb['A_ge_aI'], 'A_le_bI': nb['A_le_bI'], 'floating_lambda_min_A': nb['floating_lambda_min_A'],
            'k': r['k'], 'certified_trace_upper': r['certified_trace_upper'], 'certified_lambda_max_upper': r['certified_lambda_max_upper'],
            'resolution_1e-10': r['resolution_1e-10'], 'experimental_floating': r['experimental_floating']}


def synthetic_controls(P: dict, L: Fraction, parity: str, eps: Fraction, split: int,
                       deltas=(Fraction(1, 4), Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000))) -> dict:
    B, F, G, k_low, Y = P['B'], P['F'], P['G'], P['k'], P['Y']
    st = P['state']
    Lf, Kc = float(L), st.K
    Yf, Ff, Gf = NS.to_float(Y), NS.sym(NS.to_float(F)), NS.sym(NS.to_float(G))
    out = {'kind': 'SYNTHETIC_NOT_NATIVE', 'controls': []}
    # S1: rank-one negative term on the first low-block coordinate (C and A unchanged)
    E = K.identity(B.nrows(), 0)
    E[0, 0] = 2 * B[0, 0].mid()
    Bp = B - E
    val = K.quadratic(Bp, K.exact_vector([1] + [0] * (B.nrows() - 1)))
    _, Cp, Ap = NS.blocks(Bp, k_low)
    _, C0, A0 = NS.blocks(B, k_low)
    same = all(x.mid() == y.mid() and x.rad() == y.rad() for M1, M2 in ((Cp, C0), (Ap, A0))
               for r1, r2 in zip(M1.tolist(), M2.tolist()) for x, y in zip(r1, r2))
    out['controls'].append({'control': 'S1_low_block_rank_one', 'perturbation': 'B - 2 mid(B_00) e_1 e_1^T at the checkpoint tolerance',
                            'pencil': 'FALSIFIED_BOUND' if K.certainly_negative(val) else 'UNKNOWN_PRECISION',
                            'witness_value': K.ball_record(val), 'C_and_A_blocks_identical': same,
                            'nearband': 'IDENTICAL_TO_NATIVE_BY_CONSTRUCTION' if same else 'CHANGED'})
    # S2: two adjacent actual zeros merge and leave the line as one quartet (explicit-formula representation)
    f_split = 2 * math.pi * split / Lf
    for label, T in (('low_band', 0.5 * f_split), ('at_split', f_split), ('high_band', min(1.5 * f_split, 0.9 * 2 * math.pi * Kc / Lf))):
        n, g1, g2 = zero_pair_near(T)
        gm = (g1 + g2) / 2
        pairs = zero_form(Lf, Kc, parity, (complex(0, g1), complex(0, -g1)), Yf) + zero_form(Lf, Kc, parity, (complex(0, g2), complex(0, -g2)), Yf)
        rec = {'control': 'S2_merged_pair_offline_quartet_' + label, 'zero_indices': [n, n + 1], 'gammas': [g1, g2],
               'quartet_ordinate': gm, 'mode_index_of_ordinate': gm * Lf / (2 * math.pi), 'split': split,
               'perturbation': 'N(delta) = quartet(1/2 +- delta +- i gamma_mid) - pair(gamma_n) - pair(gamma_n+1); unscaled',
               'threshold_by_delta': []}
        for delta in deltas:
            d = float(delta)
            quartet = (complex(d, gm), complex(-d, gm), complex(d, -gm), complex(-d, -gm))
            Nf = NS.sym(zero_form(Lf, Kc, parity, quartet, Yf) - pairs)
            ev_w = NS.generalized_eig(Ff + Nf, Gf)[0]
            rec['threshold_by_delta'].append({'delta': str(delta), 'N_floating_min': float(np.linalg.eigvalsh(Nf)[0]),
                                              'floating_min_generalized_F_plus_N': float(ev_w[0]),
                                              'detection_threshold_eps_star': float(max(0.0, -ev_w[0])),
                                              'authority': 'EXPERIMENTAL_SIGNAL_FLOATING'})
        d = float(Fraction(1, 10))
        quartet = (complex(d, gm), complex(-d, gm), complex(d, -gm), complex(-d, -gm))
        Nf = NS.sym(zero_form(Lf, Kc, parity, quartet, Yf) - pairs)
        N = NS.exact(Nf)
        rec['delta_main'] = '1/10'
        rec['checkpoint'] = {'tolerance': str(eps), **certify_or_witness(B + N)}
        rec['checkpoint']['reading'] = ('CHECKPOINT_BLIND: the synthetic off-line world passes the finite checkpoint'
                                        if rec['checkpoint']['status'] == 'CERTIFIED' else 'CHECKPOINT_DETECTS')
        eps_star = next(x['detection_threshold_eps_star'] for x in rec['threshold_by_delta'] if x['delta'] == '1/10')
        if eps_star > 0:
            eps_t = NS.dyadic_below(Fraction(eps_star) / 2)
            Bn = F + K.q(eps_t) * G
            Bs = Bn + N
            rec['discrimination'] = {
                'tolerance': K.exact_str(eps_t), 'tolerance_float': float(eps_t),
                'native': {'pencil': certify_or_witness(Bn), 'nearband': nearband_summary(Bn, k_low, eps_t)},
                'synthetic': {'pencil': certify_or_witness(Bs), 'nearband': nearband_summary(Bs, k_low, eps_t)},
                'question': 'Is near-band coupling at the same tolerance different for a certified-positive native pencil and a certified-negative synthetic one?'}
        out['controls'].append(rec)
    return out


STATES = {'L4_even_half': (Fraction(4), 'even', Fraction(1, 2), 128), 'L4_odd_half': (Fraction(4), 'odd', Fraction(1, 2), 128),
          'L5_even_third': (Fraction(5), 'even', Fraction(1, 3), 312), 'L5_odd_third': (Fraction(5), 'odd', Fraction(1, 3), 312),
          'L6_even_quarter': (Fraction(6), 'even', Fraction(1, 4), 648), 'L6_odd_quarter': (Fraction(6), 'odd', Fraction(1, 4), 648)}


def run(name: str, pencil_bits: int, work_bits: int, synthetic: bool) -> dict:
    t0 = time.time()
    L, parity, eps, split = STATES[name]
    P = native_pencil(L, parity, eps, split, pencil_bits)
    ctx.prec = work_bits
    rec = {'schema': SCHEMA, **NS.CAPS, 'state_id': name, 'L': str(L), 'parity': parity, 'tolerance': str(eps),
           'split': split, 'K': P['state'].K, 'low_dimension': P['k'], 'high_dimension': P['B'].nrows() - P['k'],
           'pencil_bits': pencil_bits, 'working_bits': work_bits,
           'coordinates': 'corrected Fourier-prefix flag of E-D1 (coordinate statement; the pencil carries the full Gram)',
           'hashes': {'tool_sha256': NS.SRC.sha256(Path(__file__)), 'engine_sha256': NS.SRC.sha256(HERE / 'native_slice.py'),
                      'source_module_sha256': NS.SRC.sha256(HERE / 'native_source.py'),
                      'kernel_sha256': NS.SRC.sha256(HERE / 'certificates.py'), 'backend_sha256': NS.SRC.sha256(NS.SRC.BACKEND_PATH)}}
    rec['nearband'] = nearband_bounds(P['B'], P['k'], eps)
    if synthetic:
        rec['synthetic'] = synthetic_controls(P, L, parity, eps, split)
    rec['seconds'] = round(time.time() - t0, 1)
    return rec


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--states', required=True)
    p.add_argument('--pencil-bits', type=int, default=192)
    p.add_argument('--bits', type=int, default=512)
    p.add_argument('--synthetic', action='store_true')
    p.add_argument('--calibrate', action='store_true')
    p.add_argument('--out-dir', type=Path, required=True)
    a = p.parse_args(argv)
    a.out_dir.mkdir(parents=True, exist_ok=True)
    if a.calibrate:
        cal = {'schema': SCHEMA + '_POLE_CALIBRATION', **NS.CAPS, **pole_calibration(),
               'explicit_formula': explicit_formula_check(), 'tool_sha256': NS.SRC.sha256(Path(__file__))}
        (a.out_dir / 'pole_calibration.json').write_text(json.dumps(cal, indent=2) + '\n', encoding='utf-8')
        print(json.dumps(cal), flush=True)
    for name in [x for x in a.states.split(',') if x]:
        rec = run(name, a.pencil_bits, a.bits, a.synthetic)
        (a.out_dir / ('nearband_%s.json' % name)).write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
        nb = rec['nearband']
        print(json.dumps({'state': name, 'A_ge_aI': nb['A_ge_aI'],
                          'rows': [(r['offset_above_eps'], r['k'], r['certified_trace_upper'], r['certified_lambda_max_upper']['status'],
                                    r['experimental_floating']['trace_M_s']) for r in nb['rows']],
                          'synthetic': [(c['control'], c.get('pencil'), c.get('checkpoint', {}).get('status'),
                                         [(x['delta'], x['detection_threshold_eps_star']) for x in c.get('threshold_by_delta', [])],
                                         {k: (v['pencil']['status'], v['nearband']['certified_trace_upper'])
                                          for k, v in c.get('discrimination', {}).items() if k in ('native', 'synthetic')})
                                        for c in rec.get('synthetic', {}).get('controls', [])],
                          'seconds': rec['seconds']}), flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
