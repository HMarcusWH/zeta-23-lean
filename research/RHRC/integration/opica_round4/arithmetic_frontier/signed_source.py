"""The joint signed source -arch - prime at the native checkpoint states (Increment 3D).

M50 (PoleChannel, PROVED in Lean) shows that the pole channel vanishes on
both pole-neutral carriers, so on every moment slice the native energy is
exactly Q(u) = -Re<arch u,u> - Re<prime u,u>. This tool studies that joint
signed expression on the actual slices of E-D1 (corrected Fourier-prefix flag
basis, full Gram G):

1. channel energies (-arch, -prime) along the generalized slice spectrum of
   (F, G), and the cancellation ratio |Q| / (|arch| + |prime|) on the
   near-null directions;
2. the restrictions of -arch and -prime to the near-null subspace
   V = span{u_i : rho_i < threshold}, with G-orthonormal coordinates;
3. a prime-cutoff sweep: the slice minimum of -arch - prime_{q <= P} for P up
   to the frozen cell bound Q = floor(e^L) (atoms above Q are not native);
4. the per-prime-power contributions to Q at the bottom slice vector, ordered
   by q, with partial sums;
5. (CERTIFIED, small states) exact-witness statements about truncated-prime
   forms, computed from Arb enclosures of the truncated channel; and
6. (CERTIFIED where stated) a numerical check of the DERIVED comparison
   S_IR - S_tail = C[(q^m I - T^m)/a + (a^-1 I - A^-1)(T^m - T^2m)]C^T >= 0
   between the inverse-residual and geometric-tail families with the exact
   polynomial action P_m(A).

Items 1-4 are floating diagnostics (EXPERIMENTAL SIGNAL); the floating prime
channel is calibrated against the Arb channel (recorded). A truncated-prime
form is not a native object. RH and Step 4 remain OPEN.
"""
from __future__ import annotations

import argparse
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


NS = _load('_frontier_native_slice_ss', 'native_slice.py')
K = NS.K
from flint import arb_mat, ctx  # noqa: E402

SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_SIGNED_SOURCE_V1'
THRESHOLD = 1e-2


# ----------------------------------------------------------------------------- native slice with channels

def slice_with_channels(L: Fraction, parity: str, split: int, bits: int, atoms_max: int | None = None) -> dict:
    st = NS.SRC.NativeState(L, bits=bits)
    K.validate_state(st.Lq, st.K, st.Q, [q for q, _ in st.atoms])
    native_atoms = list(st.atoms)
    if atoms_max is not None:  # truncated prime cell: NOT native
        st.atoms = [(q, p) for q, p in native_atoms if q <= atoms_max]
        st._primitives()
    M, w, ch = st.reduced(parity, with_channels=True)
    C = st.constraints(parity)
    split_idx = split + 1 if parity == 'even' else split
    Zf, nlow = NS.flag_basis(NS.to_float(C), w, split_idx)
    Y, _ = NS.corrected(Zf, C, [(0, nlow, split_idx), (nlow, Zf.shape[1], len(w))])
    W = arb_mat([[NS.arb(w[i]) if i == j else NS.arb(0) for j in range(len(w))] for i in range(len(w))])
    Yt = Y.transpose()
    return {'state': st, 'native_atoms': native_atoms, 'Y': Y, 'k': nlow, 'weights': w,
            'F': Yt * M * Y, 'G': Yt * W * Y, 'arch': Yt * ch['arch'] * Y, 'prime': Yt * ch['prime'] * Y,
            'pole': Yt * ch['pole'] * Y, 'prime_reduced': ch['prime']}


# ----------------------------------------------------------------------------- floating prime channel by atoms

def atom_vectors(L: float, Kc: int, atoms) -> tuple[np.ndarray, np.ndarray]:
    n = np.arange(0, Kc + 1, dtype=float)
    S = np.zeros((len(atoms), Kc + 1))
    Cc = np.zeros((len(atoms), Kc + 1))
    for a, (q, p) in enumerate(atoms):
        ell, wt = math.log(q), math.log(p) / math.sqrt(q)
        t = 2 * math.pi * n * ell / L
        S[a] = wt * np.sin(t) / math.pi
        Cc[a] = 2 * wt * (1 - ell / L) * np.cos(t)
    return S, Cc


def signed_prime(S: np.ndarray, c: np.ndarray) -> np.ndarray:
    Kc = len(S) - 1
    idx = np.arange(-Kc, Kc + 1)
    Ss = np.where(idx >= 0, S[np.abs(idx)], -S[np.abs(idx)])
    diff = idx[:, None] - idx[None, :]
    with np.errstate(divide='ignore', invalid='ignore'):
        P = (Ss[None, :] - Ss[:, None]) / diff
    P[np.arange(2 * Kc + 1), np.arange(2 * Kc + 1)] = c[np.abs(idx)]
    return P


def reduce_signed(P: np.ndarray, parity: str) -> np.ndarray:
    Kc = (P.shape[0] - 1) // 2
    pos = lambda j: Kc + j
    if parity == 'even':
        idx = np.arange(0, Kc + 1)
        R = np.zeros((2 * Kc + 1, Kc + 1))
        for c, j in enumerate(idx):
            R[pos(j), c] = 1
            R[pos(-j), c] = 1
        R[pos(0), 0] = 1
    else:
        idx = np.arange(1, Kc + 1)
        R = np.zeros((2 * Kc + 1, Kc))
        for c, j in enumerate(idx):
            R[pos(j), c] = 1
            R[pos(-j), c] = -1
    return R.T @ P @ R, R


def gen_orthonormal(Gf: np.ndarray) -> np.ndarray:
    return np.linalg.inv(np.linalg.cholesky(NS.sym(Gf)))


# ----------------------------------------------------------------------------- analyses

def spectrum_channels(Ff, Gf, Af, Pf, threshold=THRESHOLD) -> dict:
    ev, U = NS.generalized_eig(Ff, Gf)  # U is G-orthonormal
    arch_e = -np.einsum('ij,ik,kj->j', U, Af, U)
    prime_e = -np.einsum('ij,ik,kj->j', U, Pf, U)
    near = ev < threshold
    ratio = np.abs(ev) / (np.abs(arch_e) + np.abs(prime_e))
    sample = sorted(set(list(range(0, min(5, len(ev)))) + [int(near.sum()) - 1, int(near.sum()), len(ev) - 1]))
    V = U[:, near]
    Ra, Rp = NS.sym(-V.T @ Af @ V), NS.sym(-V.T @ Pf @ V)
    ea, ep = np.linalg.eigvalsh(Ra), np.linalg.eigvalsh(Rp)
    return {
        'authority': 'EXPERIMENTAL_SIGNAL_FLOATING',
        'threshold': threshold, 'near_null_count': int(near.sum()), 'dimension': len(ev),
        'bottom_eigenvalues': [float(x) for x in ev[:5]],
        'samples': [{'index': i, 'rho': float(ev[i]), 'minus_arch': float(arch_e[i]), 'minus_prime': float(prime_e[i])} for i in sample if 0 <= i < len(ev)],
        'near_null_cancellation': {
            'max_ratio_Q_over_channel_sizes': float(ratio[near].max()) if near.any() else None,
            'median_channel_size': float(np.median(np.abs(arch_e[near]))) if near.any() else None,
            'minus_arch_energy_range': [float(arch_e[near].min()), float(arch_e[near].max())] if near.any() else None},
        'restriction_to_near_null_subspace': {
            'minus_arch_extremes': [float(ea[0]), float(ea[-1])], 'minus_prime_extremes': [float(ep[0]), float(ep[-1])],
            'minus_arch_negative_count': int((ea < 0).sum()), 'minus_prime_negative_count': int((ep < 0).sum()),
            'joint_Q_restricted_extremes': [float(np.linalg.eigvalsh(Ra + Rp)[0]), float(np.linalg.eigvalsh(Ra + Rp)[-1])],
            'reading': 'on V the two channels cancel to the size of the joint energy; each channel alone is controlled only through the other'},
        '_U0': U[:, 0]}


def prime_sweep(Ff, Gf, Yf, parity, Lf, Kc, atoms, Pf_all, grid) -> list:
    S, Cc = atom_vectors(Lf, Kc, atoms)
    qs = np.array([q for q, _ in atoms])
    out = []
    for P in grid:
        sel = qs <= P
        Pred, _ = reduce_signed(signed_prime(S[sel].sum(axis=0), Cc[sel].sum(axis=0)), parity) if sel.any() else (np.zeros((Yf.shape[0],) * 2), None)
        FP = NS.sym(Ff + Pf_all - Yf.T @ Pred @ Yf)  # -arch - prime_{<=P}
        ev = NS.generalized_eig(FP, Gf)[0]
        out.append({'prime_cutoff': int(P), 'atoms_included': int(sel.sum()), 'slice_min': float(ev[0]),
                    'negative_count': int((ev < -1e-12).sum()), 'slice_max': float(ev[-1])})
    return out


def atom_contributions(u_red: np.ndarray, parity, Lf, Kc, atoms, arch_value: float) -> dict:
    """Per-atom -prime_a(u,u) at the bottom vector, in signed coordinates."""
    S, Cc = atom_vectors(Lf, Kc, atoms)
    idx = np.arange(-Kc, Kc + 1)
    if parity == 'even':
        x = u_red[np.abs(idx)]
    else:
        x = np.where(idx > 0, 1.0, -1.0) * np.where(idx == 0, 0.0, u_red[np.maximum(np.abs(idx) - 1, 0)])
    diff = idx[:, None] - idx[None, :]
    with np.errstate(divide='ignore'):
        H = np.where(diff != 0, 1.0 / np.where(diff == 0, 1, diff), 0.0)
    g = H.T @ x
    vals = []
    for a in range(len(atoms)):
        Ss = np.where(idx >= 0, S[a][np.abs(idx)], -S[a][np.abs(idx)])
        v = -2 * float(g @ (Ss * x)) - float(np.sum(Cc[a][np.abs(idx)] * x * x))
        vals.append(v)
    vals = np.array(vals)
    order = np.argsort(-np.abs(vals))
    partial = np.cumsum(vals)
    return {'authority': 'EXPERIMENTAL_SIGNAL_FLOATING', 'vector': 'bottom generalized eigenvector of (F, G), G-normalized',
            'minus_arch': arch_value, 'minus_prime_total': float(vals.sum()), 'joint': arch_value + float(vals.sum()),
            'largest_atoms': [{'q': atoms[i][0], 'p': atoms[i][1], 'minus_prime_a': float(vals[i])} for i in order[:12]],
            'partial_sums_by_q': [{'q_max': atoms[i][0], 'minus_arch_plus_partial': arch_value + float(partial[i])}
                                  for i in sorted(set([0, 1, 2, 4, 9, 19, len(atoms) // 4, len(atoms) // 2, len(atoms) - 1])) if i < len(atoms)],
            'positive_atoms': int((vals > 0).sum()), 'negative_atoms': int((vals < 0).sum()),
            'sum_abs_over_abs_sum': float(np.abs(vals).sum() / max(abs(vals.sum()), 1e-300))}


def certified_truncation(L, parity, split, bits, P, native_bottom=None) -> dict:
    """Exact-witness status of the truncated-prime slice form -arch - prime_{q <= P} (NOT native)."""
    T = slice_with_channels(L, parity, split, bits, atoms_max=P)
    F, G = T['F'], T['G']
    Ff, Gf = NS.sym(NS.to_float(F)), NS.sym(NS.to_float(G))
    ev, U = NS.generalized_eig(Ff, Gf)
    rec = {'prime_cutoff': P, 'atoms_included': len(T['state'].atoms), 'floating_min': float(ev[0]), 'kind': 'TRUNCATED_PRIME_CELL_NOT_NATIVE'}
    if ev[0] < 0:
        val = K.quadratic(F, NS.exact_col(U[:, 0]))
        rec['status'] = 'FALSIFIED_BOUND' if K.certainly_negative(val) else 'UNKNOWN_PRECISION'
        rec['witness_value'] = K.ball_record(val)
        rec['statement'] = 'the truncated form takes a certainly negative value at an exact slice vector'
    else:
        rec['status'] = 'NOT_REFUTED_BY_THIS_WITNESS'
    return rec


def derived_family_check(B: arb_mat, k_low: int, m: int) -> dict:
    D, C, A = NS.blocks(B, k_low)
    Af = NS.sym(NS.to_float(A))
    lam = np.linalg.eigvalsh(Af)
    a = NS.rational_below(0.98 * lam[0], 10 ** 6)
    b = NS.rational_above(1.02 * lam[-1], 1000)
    P = K.polynomial_action(A, b, m)  # enclosure of the exact P_m(A)
    X = P * C.transpose()
    S_ir = K.inverse_residual_form(B, k_low, a, X)
    S_tail = D - C * P * C.transpose() - C * C.transpose() * K.q((1 - a / b) ** m / a)
    Diff = K.symmetrized(S_ir - S_tail)
    Dfl = NS.sym(NS.to_float(Diff))
    # closed form in floating arithmetic
    q = 1 - float(a) / float(b)
    T = np.eye(len(lam)) - Af / float(b)
    Tm = np.linalg.matrix_power(T, m)
    Cf = NS.to_float(C)
    rhs = Cf @ ((q ** m * np.eye(len(lam)) - Tm) / float(a) + (np.eye(len(lam)) / float(a) - np.linalg.inv(Af)) @ (Tm - Tm @ Tm)) @ Cf.T
    ev = np.linalg.eigvalsh(Dfl)
    out = {'degree': m, 'a': str(a), 'b': str(b), 'floating_min_eig': float(ev[0]), 'floating_max_eig': float(ev[-1]),
           'closed_form_relative_error': float(np.abs(Dfl - NS.sym(rhs)).max() / max(np.abs(Dfl).max(), 1e-300)),
           'identity': 'S_IR(X = P_m(A) C^T) - S_tail = C[(q^m I - T^m)/a + (a^-1 I - A^-1)(T^m - T^2m)]C^T (DERIVED, exact P_m, aI <= A <= bI)'}
    # certified route: Diff = C Mid C^T as enclosures, with Mid > 0 certified (Diff is only semidefinite when C is rank deficient)
    n = A.nrows()
    Ta = K.identity(n) - A * (1 / K.q(b))
    Tm_a = K.identity(n)
    for _ in range(m):
        Tm_a = Tm_a * Ta
    Mid = K.symmetrized((K.identity(n, K.q((1 - a / b) ** m)) - Tm_a) * (1 / K.q(a))
                        + (K.identity(n, 1 / K.q(a)) - A.inv()) * (Tm_a - Tm_a * Tm_a))
    E = Diff - C * Mid * C.transpose()
    contains = all(x.contains(0) for row in E.tolist() for x in row)
    mid_ev = np.linalg.eigvalsh(NS.sym(NS.to_float(Mid)))
    mid_cert = NS.certify(Mid, NS.dyadic_below(mid_ev[0] / 2)) if mid_ev[0] > 0 else {'status': 'NOT_ATTEMPTED'}
    out['middle_floating_min'] = float(mid_ev[0])
    out['middle_certificate'] = mid_cert['status']
    out['factorization_enclosure_contains_zero'] = contains
    out['certificate'] = ('CERTIFIED_PSD_VIA_FACTORIZATION' if contains and mid_cert['status'] == 'CERTIFIED'
                          else 'NOT_CERTIFIED')
    out['certificate_statement'] = 'S_IR - S_tail = C Mid C^T (enclosure identity) and Mid > 0 (kernel certificate), hence S_IR - S_tail >= 0'
    out['reading'] = 'at the same exact degree the inverse-residual Schur form dominates the geometric-tail form'
    return out


STATES = {'L4_even': (Fraction(4), 'even', Fraction(1, 2), 128), 'L4_odd': (Fraction(4), 'odd', Fraction(1, 2), 128),
          'L5_even': (Fraction(5), 'even', Fraction(1, 3), 312), 'L5_odd': (Fraction(5), 'odd', Fraction(1, 3), 312),
          'L6_even': (Fraction(6), 'even', Fraction(1, 4), 648), 'L6_odd': (Fraction(6), 'odd', Fraction(1, 4), 648)}


def run(name: str, bits: int, certify_truncations: bool, family_degrees=()) -> dict:
    t0 = time.time()
    L, parity, eps, split = STATES[name]
    P = slice_with_channels(L, parity, split, bits)
    st = P['state']
    Lf, Kc = float(L), st.K
    Yf = NS.to_float(P['Y'])
    Ff, Gf = NS.sym(NS.to_float(P['F'])), NS.sym(NS.to_float(P['G']))
    Af, Pf = NS.sym(NS.to_float(P['arch'])), NS.sym(NS.to_float(P['prime']))
    pole_max = float(np.abs(NS.to_float(P['pole'])).max())
    atoms = P['native_atoms']
    S, Cc = atom_vectors(Lf, Kc, atoms)
    Pred, _ = reduce_signed(signed_prime(S.sum(axis=0), Cc.sum(axis=0)), parity)
    calib = float(np.abs(Pred - NS.to_float(P['prime_reduced'])).max() / np.abs(NS.to_float(P['prime_reduced'])).max())
    rec = {'schema': SCHEMA, **NS.CAPS, 'state_id': name, 'L': str(L), 'parity': parity, 'K': Kc, 'Q': st.Q, 'atoms': len(atoms),
           'split': split, 'bits': bits, 'dimension': P['F'].nrows(),
           'hashes': {'tool_sha256': NS.SRC.sha256(Path(__file__)), 'engine_sha256': NS.SRC.sha256(HERE / 'native_slice.py'),
                      'source_module_sha256': NS.SRC.sha256(HERE / 'native_source.py'),
                      'kernel_sha256': NS.SRC.sha256(HERE / 'certificates.py'), 'backend_sha256': NS.SRC.sha256(NS.SRC.BACKEND_PATH)},
           'pole_on_slice_max_abs_float': pole_max,
           'pole_statement': 'M50 (Lean): the pole channel vanishes on the slice; the floating restriction is at rounding size',
           'floating_prime_calibration_relative_error': calib,
           'energy_identity_float_error': float(np.abs(Ff - (-Af - Pf + NS.to_float(P['pole']))).max() / np.abs(Ff).max())}
    sc = spectrum_channels(Ff, Gf, Af, Pf)
    u0 = sc.pop('_U0')
    rec['spectrum_channels'] = sc
    top = [q for q, _ in atoms]
    drop_top = [top[-1 - j] for j in (1, 2, 3) if len(top) > j]  # cutoffs excluding only the top j atoms
    qs = sorted(set([2, 3, 5, 10, 20, 50, 100, 200, 500, 1000, st.Q] + drop_top))
    grid = [0] + [x for x in qs if x <= st.Q]
    rec['prime_cutoff_sweep'] = {'authority': 'EXPERIMENTAL_SIGNAL_FLOATING', 'form': '-arch - prime_{q <= P} on the native slice (P < Q is not native)',
                                 'top_atoms': top[-4:], 'cutoffs_dropping_only_the_top_atoms': drop_top,
                                 'rows': prime_sweep(Ff, Gf, Yf, parity, Lf, Kc, atoms, Pf, grid)}
    u_red = Yf @ u0
    arch_val = float(-u0 @ Af @ u0)
    rec['bottom_vector_atoms'] = atom_contributions(u_red, parity, Lf, Kc, atoms, arch_val)
    rec['bottom_vector_atoms']['minus_prime_from_slice_matrix'] = float(-u0 @ Pf @ u0)
    if certify_truncations:
        rows = rec['prime_cutoff_sweep']['rows']
        cands = [0] + ([drop_top[0]] if drop_top and any(r['prime_cutoff'] == drop_top[0] and r['slice_min'] < 0 for r in rows) else [])
        rec['certified_truncations'] = [certified_truncation(L, parity, split, bits, c) for c in cands]
    if family_degrees:
        B = P['F'] + K.q(eps) * P['G']
        ctx.prec = max(bits, 256)
        rec['derived_family_comparison'] = {'tolerance': str(eps),
                                            'rows': [derived_family_check(B, P['k'], m) for m in family_degrees]}
    rec['seconds'] = round(time.time() - t0, 1)
    return rec


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--states', required=True)
    p.add_argument('--bits', type=int, default=192)
    p.add_argument('--certify-truncations', action='store_true')
    p.add_argument('--family-degrees', default='')
    p.add_argument('--out-dir', type=Path, required=True)
    a = p.parse_args(argv)
    a.out_dir.mkdir(parents=True, exist_ok=True)
    fam = tuple(int(x) for x in a.family_degrees.split(',') if x)
    for name in a.states.split(','):
        rec = run(name, a.bits, a.certify_truncations, fam)
        (a.out_dir / ('signed_%s.json' % name)).write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
        sc = rec['spectrum_channels']
        print(json.dumps({'state': name, 'calib': rec['floating_prime_calibration_relative_error'], 'pole': rec['pole_on_slice_max_abs_float'],
                          'near': sc['near_null_count'], 'restr': sc['restriction_to_near_null_subspace'],
                          'sweep': [(r['prime_cutoff'], r['slice_min'], r['negative_count']) for r in rec['prime_cutoff_sweep']['rows']],
                          'trunc': [(r['prime_cutoff'], r['status']) for r in rec.get('certified_truncations', [])],
                          'family': [(r['degree'], r['floating_min_eig'], r['closed_form_relative_error'], r['certificate'])
                                     for r in rec.get('derived_family_comparison', {}).get('rows', [])],
                          'seconds': rec['seconds']}), flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
