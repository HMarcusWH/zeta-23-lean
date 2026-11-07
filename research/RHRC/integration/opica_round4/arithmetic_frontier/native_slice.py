"""Native moment-slice discovery engine, version 2 (Increment 2B).

Floating linear algebra (numpy) only *proposes*: bases, factors, inverse
actions and witness vectors. Every acceptance or falsification decision is
made by the floating-point-free kernel ``certificates.py`` on exact dyadic
proposals and Arb enclosures of the source from ``native_source.py``.

The carriers are the Lean moment slices of
``Zeta23.OPICARound4.ArithmeticFrontier``. The corrected basis is the exact
object Y_* = Z - E_P (C E_P)^-1 C Z (pivot block certified invertible), so
C Y_* = 0 holds algebraically; its full physical Gram G, including every cross
block, is carried and certified positive. Physical statements use the pencil
F + eps G. Block statements are labelled COORDINATE (the corrected flag basis
is an orthonormal proposal, not exactly orthonormal) or PHYSICAL (relative to
the block's own Gram).

Version 1 (Increment 2) is preserved byte for byte at
``evidence/increment2/producer/native_slice.py`` with its records.
Research certification, not Lean authority. RH and Step 4 remain OPEN.
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
from flint import arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent


def _load(name: str, file: str):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SRC = _load('_frontier_native_source', 'native_source.py')
K = _load('_frontier_certificates', 'certificates.py')
REPO = SRC.REPO
CAPS = {'RH': 'OPEN', 'Step4': 'OPEN', 'authority': 'RESEARCH_CERTIFICATION_NOT_LEAN_AUTHORITY'}
SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_NATIVE_SLICE_RUN_V2'
THRESHOLDS = (2, 4, 6, 8, 10, 12, 13)


# ----------------------------------------------------------------------------- float <-> exact

def to_float(m: arb_mat) -> np.ndarray:
    return np.array([[float(x.mid()) for x in row] for row in m.tolist()], dtype=float)


def exact(a: np.ndarray) -> arb_mat:
    """Exact ball matrix of a finite float array (binary conversion is exact)."""
    a = np.atleast_2d(a)
    if not np.all(np.isfinite(a)):
        raise K.InvalidCertificateInput('non-finite proposal')
    return arb_mat([[arb(float(x)) for x in row] for row in a])


def exact_col(v: np.ndarray) -> arb_mat:
    return exact(np.asarray(v, dtype=float).reshape(-1, 1))


def sym(a: np.ndarray) -> np.ndarray:
    return (a + a.T) / 2


def array_sha256(a: np.ndarray) -> str:
    return hashlib.sha256(np.ascontiguousarray(a, dtype='<f8').tobytes()).hexdigest()


def rational_below(x: float, digits: int) -> Fraction:
    return Fraction(math.floor(x * digits), digits)


def rational_above(x: float, digits: int) -> Fraction:
    return Fraction(math.ceil(x * digits), digits)


def dyadic_below(x) -> Fraction:
    """Largest power of two not above x > 0 (exact for Fractions of any size)."""
    x = Fraction(x)
    if not x > 0:
        raise K.InvalidCertificateInput('dyadic_below needs a positive value')
    e = x.numerator.bit_length() - x.denominator.bit_length()
    p = lambda k: Fraction(2) ** k if k >= 0 else Fraction(1, 2 ** (-k))
    while p(e) > x:
        e -= 1
    while p(e + 1) <= x:
        e += 1
    return p(e)


# ----------------------------------------------------------------------------- proposals

def pivots_for(C: np.ndarray, allowed: int) -> list[int]:
    A = C[:, :allowed] / np.linalg.norm(C[:, :allowed], axis=1, keepdims=True)
    chosen, basis = [], []
    for _ in range(A.shape[0]):
        R = A.copy()
        for qv in basis:
            R -= np.outer(qv, qv @ R)
        norms = np.linalg.norm(R, axis=0)
        norms[chosen] = -1
        j = int(np.argmax(norms))
        chosen.append(j)
        basis.append(R[:, j] / norms[j])
    return chosen


def kernel_basis(C: np.ndarray, weights: list[int], prefix: int, start: int = 0) -> np.ndarray:
    """W-orthonormal floating basis of the constraint kernel on indices in [start, prefix)."""
    dim = C.shape[1]
    w = np.sqrt(np.array(weights[start:prefix], dtype=float))
    Cs = C[:, start:prefix] / np.linalg.norm(C[:, start:prefix], axis=1, keepdims=True) / w
    qm, _ = np.linalg.qr(Cs.T, mode='complete')
    Z = np.zeros((dim, (prefix - start) - C.shape[0]))
    Z[start:prefix] = qm[:, C.shape[0]:] / w[:, None]
    return Z


def flag_basis(C: np.ndarray, weights: list[int], split: int | None) -> tuple[np.ndarray, int]:
    dim = C.shape[1]
    full = kernel_basis(C, weights, dim)
    if split is None:
        return full, 0
    low = kernel_basis(C, weights, split)
    W = np.array(weights, dtype=float)
    rest = full - low @ (low.T @ (W[:, None] * full))
    u, _, _ = np.linalg.svd(np.sqrt(W)[:, None] * rest, full_matrices=False)
    high = u[:, :full.shape[1] - low.shape[1]] / np.sqrt(W)[:, None]
    return np.hstack([low, high]), low.shape[1]


def corrected(Zf: np.ndarray, C: arb_mat, groups: list[tuple[int, int, int]]) -> tuple[arb_mat, list]:
    """Exact corrected basis by column group (first, last, prefix); pivots inside each prefix."""
    Cf = to_float(C)
    cols, recipe = [], []
    for first, last, prefix in groups:
        piv = pivots_for(Cf, prefix)
        Y = K.corrected_basis(exact(Zf[:, first:last]), C, piv)
        cols.append(Y)
        recipe.append({'columns': [first, last], 'prefix': prefix, 'pivots': piv})
    rows = [sum((Y.tolist()[i] for Y in cols), []) for i in range(C.ncols())]
    return arb_mat(rows), recipe


def float_factor(Af: np.ndarray, tau: Fraction) -> arb_mat | None:
    try:
        return exact(np.linalg.cholesky(sym(Af) - float(tau) * np.eye(Af.shape[0])))
    except np.linalg.LinAlgError:
        return None


def certify(A: arb_mat, tau: Fraction, Af: np.ndarray | None = None) -> dict:
    """Kernel certificate of A > 0 at shift tau with a floating factor proposal."""
    Af = to_float(A) if Af is None else Af
    R = float_factor(Af, tau)
    if R is None:
        return {'status': 'UNKNOWN_PRECISION', 'reason': 'floating shifted factorization failed', 'tau': str(tau)}
    return K.certify_shifted(A, tau, R)


def form_status(S: arb_mat, label: str) -> dict:
    """Certify S > 0, or falsify the sufficient inequality S >= 0 with an exact vector."""
    Sf = sym(to_float(S))
    ev, vec = np.linalg.eigh(Sf)
    if ev[0] > 0:
        out = certify(S, dyadic_below(ev[0] / 2), Sf)
    else:
        val = K.quadratic(S, exact_col(vec[:, 0]))
        out = {'status': 'FALSIFIED_BOUND' if K.certainly_negative(val) else 'UNKNOWN_PRECISION',
               'witness_value': K.ball_record(val), 'witness_kind': 'EXACT_DYADIC_FLOATING_EIGENVECTOR'}
    out['statement'] = label
    out['floating_minimum'] = float(ev[0])
    return out


def bound_test(A: arb_mat, a: Fraction, which: str, G: arb_mat | None = None) -> dict:
    """A >= a G or A <= a G: CERTIFIED by a kernel certificate, FALSIFIED only by an exact vector."""
    Gm = G if G is not None else K.identity(A.nrows())
    Af, Gf = sym(to_float(A)), sym(to_float(Gm))
    S = (A - K.q(a) * Gm) if which == 'lower' else (K.q(a) * Gm - A)
    Sf = sym(Af - float(a) * Gf) if which == 'lower' else sym(float(a) * Gf - Af)
    ev, vec = np.linalg.eigh(Sf)
    if ev[0] > 0:
        out = certify(S, dyadic_below(ev[0] / 2), Sf)
    else:
        v = exact_col(vec[:, 0])
        rec = (K.refute_lower if which == 'lower' else K.refute_upper)(A, a, v, G)
        out = {'status': 'FALSIFIED_BOUND' if rec['status'] == 'FALSIFIED_BOUND' else 'UNKNOWN_PRECISION',
               'witness_value': rec['witness_value']}
    out['bound'] = ('A >= %s' if which == 'lower' else 'A <= %s') % a + (' G' if G is not None else ' I')
    return out


def generalized_eig(Ff: np.ndarray, Gf: np.ndarray):
    Li = np.linalg.inv(np.linalg.cholesky(sym(Gf)))
    ev, U = np.linalg.eigh(Li @ sym(Ff) @ Li.T)
    return ev, Li.T @ U


def main_term_N(T: float) -> float:
    t = T / (2 * math.pi)
    return t * math.log(t) - t + 7 / 8


def spectral_stats(ev: np.ndarray, dim: int, K_: int, L: Fraction) -> dict:
    T = 2 * math.pi * K_ / float(L)
    return {'authority': 'EXPERIMENTAL_SIGNAL_FLOATING_ONLY',
            'abs_below_10^-t': {str(t): int(np.sum(np.abs(ev) < 10.0 ** -t)) for t in THRESHOLDS},
            'signed_below_10^-t': {str(t): int(np.sum(ev < 10.0 ** -t)) for t in THRESHOLDS},
            'floating_negative_count': int(np.sum(ev < 0)),
            'floating_negative_below_-1e-12': int(np.sum(ev < -1e-12)),
            'undecided_note': 'floating eigenvalues within about 1e-14 of zero are not sign-resolved',
            'T': T, 'N_main_T': main_term_N(T), 'dim_minus_N_main_T': dim - main_term_N(T),
            'N_main_definition': '(T/2pi) log(T/2pi) - T/2pi + 7/8; main terms only, not a certified zero count',
            'lowest': [float(x) for x in ev[:6]], 'highest': float(ev[-1])}


# ----------------------------------------------------------------------------- run

def slice_run(L: Fraction, parity: str, eps_list=(), split: int | None = None, bits: int = 192,
              margins=(), K_: int | None = None, bracket: bool = False, degrees=(64,),
              tail_degrees=(64,), high_support: bool = True) -> dict:
    t0 = time.time()
    st = SRC.NativeState(L, K=K_, bits=bits)
    if K_ is None:
        K.validate_state(st.Lq, st.K, st.Q, [q for q, _ in st.atoms])
    M, weights, chans = st.reduced(parity, with_channels=True)
    C = st.constraints(parity)
    Cf = to_float(C)
    dim_expected = st.K - 3 if parity == 'even' else st.K - 4
    split_idx = None if split is None else (split + 1 if parity == 'even' else split)
    Zf, nlow = flag_basis(Cf, weights, split_idx)
    if Zf.shape[1] != dim_expected:
        raise ArithmeticError('proposed basis dimension differs from the proved slice dimension')
    groups = [(0, nlow, split_idx), (nlow, Zf.shape[1], len(weights))] if nlow else [(0, Zf.shape[1], len(weights))]
    Y, recipe = corrected(Zf, C, groups)
    W = arb_mat([[arb(weights[i]) if i == j else arb(0) for j in range(len(weights))] for i in range(len(weights))])
    F = Y.transpose() * M * Y
    G = Y.transpose() * W * Y
    Ff, Gf = sym(to_float(F)), sym(to_float(G))
    gram = certify(G, Fraction(1, 4), Gf)
    if gram['status'] != 'CERTIFIED':
        raise ArithmeticError('full Gram not certified positive; rank not established')
    ev, U = generalized_eig(Ff, Gf)
    xb = exact_col(U[:, 0])
    energy, norm = K.quadratic(F, xb), K.quadratic(G, xb)
    xs = Y * xb
    budget = {k: (xs.transpose() * chans[k] * xs)[0, 0] for k in ('pole', 'arch', 'prime')}
    channel = {}
    for name, sign, key in (('pole', 1, 'pole'), ('minus_arch', -1, 'arch'), ('minus_prime', -1, 'prime')):
        Pm = Y.transpose() * chans[key] * Y
        evc, Uc = generalized_eig(sign * to_float(Pm), Gf)
        w = exact_col(Uc[:, 0])
        channel[name] = {'floating_min': float(evc[0]), 'floating_max': float(evc[-1]),
                         'rayleigh_at_min_vector': K.ball_record(sign * K.rayleigh(Pm, w, G))}
    rec = {
        'schema': SCHEMA, **CAPS,
        'state': {'L_exact': str(st.Lq), 'cutoff_expression': 'originalDetectorQuarticCutoff(L)=ceil(L^4)' if K_ is None else 'EXPLICIT_K',
                  'K': st.K, 'Q': st.Q, 'prime_powers': [q for q, _ in st.atoms], 'parity': parity,
                  'carrier': 'evenMomentSlice' if parity == 'even' else 'oddMomentSlice', 'dimension': Zf.shape[1],
                  'metric': 'PHYSICAL_INHERITED_EUCLIDEAN', 'state_kind': 'ACTUAL_STATE', 'state_validated': K_ is None},
        'precision_bits': bits,
        'source': {'backend': str(SRC.BACKEND_PATH.relative_to(REPO)), 'backend_sha256': SRC.sha256(SRC.BACKEND_PATH),
                   'source_module_sha256': SRC.sha256(HERE / 'native_source.py'),
                   'kernel_sha256': SRC.sha256(HERE / 'certificates.py'), 'engine_sha256': SRC.sha256(Path(__file__)),
                   'versions': {'python_flint': __import__('flint').__version__, 'numpy': np.__version__, 'python': sys.version.split()[0]}},
        'basis': {'definition': 'Y_* = Z - E_P (C E_P)^-1 C Z per column group; C Y_* = 0 algebraically; pivot blocks certified invertible',
                  'proposal_kind': 'FLOAT_W_ORTHONORMAL_PROPOSAL (not exactly orthonormal)', 'recipe': recipe,
                  'full_gram_certificate': gram, 'flag_split_index': split, 'low_dimension': nlow,
                  'realification': K.realification_adapter()},
        'hashes': {'proposal_Z_float64_sha256': array_sha256(Zf), 'gram_enclosure_sha256': K.enclosure_sha256(G),
                   'form_enclosure_sha256': K.enclosure_sha256(F),
                   'prime_power_list_sha256': hashlib.sha256(json.dumps([q for q, _ in st.atoms]).encode()).hexdigest()},
        'assurance': {'integrity': 'record hashes', 'certificate': 'PRODUCER_IN_PROCESS_VIA_KERNEL',
                      'independent_reconstruction': 'see INDEPENDENT_RECONSTRUCTION records where present',
                      'lean_bridge': 'OPEN (FiniteCertificateSoundness, native enclosure bridge)'},
        'endpoint_certificates': [],
        'spectral_statistics': spectral_stats(ev, Zf.shape[1], st.K, st.Lq),
        'channel_extremes_on_slice': {**channel, 'meaning': 'each channel alone on the same slice and physical metric',
                                      'authority': 'FLOATING_SPECTRA_WITH_ONE_ENCLOSED_RAYLEIGH_VALUE_PER_CHANNEL'},
        'bottom_vector_budget': {'rayleigh_upper': K.ball_record(energy / norm), 'pole': K.ball_record(budget['pole']),
                                 'arch': K.ball_record(budget['arch']), 'prime': K.ball_record(budget['prime']),
                                 'energy': K.ball_record(energy), 'physical_norm_sq': K.ball_record(norm),
                                 'scope': 'one exact slice vector; an upper bound on the slice minimum, never a lower bound'},
    }
    if bracket:
        rec['bottom_bracket'] = bottom_bracket(F, G, U[:, 0])
    for eps in eps_list:
        eps = Fraction(eps)
        B = F + K.q(eps) * G
        cert = certify(B, eps / 2, sym(Ff + float(eps) * Gf))
        rec['endpoint_certificates'].append({'target_id': 'C1_CHECKPOINT_TOLERANCE', 'tolerance': str(eps),
            'statement': 'Q_p(L,x) >= -%s ||x||^2 for every x in the slice (physical norm)' % eps, **cert})
    for m in margins:
        rec['endpoint_certificates'].append(certify_margin(F, G, Fraction(m), U[:, 0]))
    if split is not None:
        rec['block_tests'] = [block_tests(F, G, nlow, Fraction(eps), degrees, tail_degrees) for eps in eps_list]
    if high_support and split_idx is not None:
        rec['high_support_unshifted'] = high_support_test(M, W, C, weights, split_idx)
    rec['seconds'] = round(time.time() - t0, 1)
    return rec


def certify_margin(F: arb_mat, G: arb_mat, m: Fraction, u0: np.ndarray) -> dict:
    out = {'target_id': 'SLICE_POSITIVE_MARGIN', 'margin': str(m),
           'statement': 'Q_p(L,x) >= %s ||x||^2 for every x in the slice' % m}
    x = inverse_iteration(F, G, u0)
    ref = K.refute_lower(F, m, x, G)
    if ref['status'] == 'FALSIFIED_BOUND':
        return {**out, 'status': 'FALSIFIED_BOUND', 'witness_value': ref['witness_value']}
    rho = K.rayleigh(F, x, G)
    gap = K.lower(rho) - m
    if not gap > 0:
        return {**out, 'status': 'UNKNOWN_PRECISION', 'reason': 'margin not separated from the Rayleigh value'}
    tau = dyadic_below(gap / 4)
    return {**out, **K.certify_shifted(F - K.q(m) * G, tau)}


def inverse_iteration(F: arb_mat, G: arb_mat, u0: np.ndarray, iterations: int = 4) -> arb_mat:
    Fm = arb_mat([[x.mid() for x in row] for row in F.tolist()])
    Gm = arb_mat([[x.mid() for x in row] for row in G.tolist()])
    x = exact_col(u0)
    for _ in range(iterations):
        y = Fm.solve(Gm * x, algorithm='approx')
        s = (y.transpose() * y)[0, 0].mid().sqrt().mid()
        x = arb_mat([[(y[i, 0] / s).mid()] for i in range(y.nrows())])
    return x


def bottom_bracket(F: arb_mat, G: arb_mat, u0: np.ndarray) -> dict:
    x = inverse_iteration(F, G, u0)
    rho = K.rayleigh(F, x, G)
    out = {'target_id': 'SLICE_BOTTOM_BRACKET', 'rayleigh_upper': K.ball_record(rho)}
    if not K.certainly_positive(rho):
        return {**out, 'status': 'UPPER_ONLY', 'reason': 'Rayleigh value not certainly positive'}
    m = dyadic_below(K.lower(rho) / 4)
    cert = K.certify_shifted(F - K.q(m) * G, m)
    return {**out, 'margin_lower': K.exact_str(m), 'margin_certificate': cert,
            'status': 'BRACKETED' if cert['status'] == 'CERTIFIED' else 'UPPER_ONLY',
            'statement': 'm ||x||^2 <= Q_p(L,x) on the whole slice, and an exact vector attains <= rho ||x||^2'}


def blocks(M: arb_mat, k: int):
    rows = M.tolist()
    return (arb_mat([r[:k] for r in rows[:k]]), arb_mat([r[k:] for r in rows[:k]]), arb_mat([r[k:] for r in rows[k:]]))


def block_tests(F: arb_mat, G: arb_mat, k: int, eps: Fraction, degrees, tail_degrees) -> dict:
    B = F + K.q(eps) * G
    D, C, A = blocks(B, k)
    _, _, A0 = blocks(F, k)
    _, _, Ghh = blocks(G, k)
    Af, Cf, Df = sym(to_float(A)), to_float(C), sym(to_float(D))
    ea, va = np.linalg.eigh(Af)
    ep, vp = generalized_eig(Af, sym(to_float(Ghh)))
    out = {'target_tolerance': str(eps), 'low_dimension': k, 'high_dimension': A.nrows(),
           'decomposition': 'FOURIER_PREFIX_FLAG: low = slice through the split; high = corrected complement proposal (not exactly G-orthogonal)',
           'coordinate_high_extremes': [float(ea[0]), float(ea[-1])],
           'physical_high_extremes_relative_to_G_hh': [float(ep[0]), float(ep[-1])]}
    wh = exact_col(va[:, 0])
    out['coordinate_high_rayleigh'] = K.ball_record(K.rayleigh(A, wh))
    out['unshifted_prefix_complement'] = {
        'coordinate_rayleigh': K.ball_record(K.rayleigh(A0, exact_col(np.linalg.eigh(sym(to_float(A0)))[1][:, 0]))),
        'physical_rayleigh': K.ball_record(K.rayleigh(A0, exact_col(generalized_eig(sym(to_float(A0)), sym(to_float(Ghh)))[1][:, 0]), Ghh)),
        'scope': 'upper bounds on the minimum of the unshifted prefix-complement block; FOURIER_PREFIX_COMPLEMENT, not high support'}
    out['SHIFTED_PREFIX_QUARTER_GAP_COORDINATE'] = bound_test(A, Fraction(1, 4), 'lower')
    bounds = [('REPORTED_L4_HALF_CONSTANTS_COORDINATE', Fraction(49, 100), Fraction(9))]
    if ea[0] > 0:
        bounds.append(('SUGGESTED_COORDINATE', rational_below(0.98 * ea[0], 10 ** 6), rational_above(1.02 * ea[-1], 1000)))
    out['high_block_bounds'] = []
    certified_a = None
    for label, a, b in bounds:
        lo, hi = bound_test(A, a, 'lower'), bound_test(A, b, 'upper')
        out['high_block_bounds'].append({'label': label, 'a': str(a), 'b': str(b), 'a_le_A': lo, 'A_le_b': hi})
        if certified_a is None and lo['status'] == 'CERTIFIED':
            certified_a = (label, a, b, hi['status'])
    # scalar gap for every admissible a
    rho_f = float(K.upper(K.rayleigh(A, wh)))
    vs = np.linalg.eigh(Df - Cf @ Cf.T / rho_f)[1][:, 0] if rho_f > 0 else None
    out['SCALAR_GAP'] = (K.refute_scalar_gap_for_all(B, k, wh, exact_col(vs)) if vs is not None
                         else {'family': 'SCALAR_GAP', 'status': 'NOT_ELIGIBLE'})
    out['INVERSE_RESIDUAL'] = []
    out['GEOMETRIC_TAIL'] = []
    if certified_a is None:
        out['INVERSE_RESIDUAL'].append({'status': 'NOT_ELIGIBLE', 'reason': 'no certified A >= a I with a > 0'})
    else:
        label, a, b, cap = certified_a
        pre_R = float_factor(Af - float(a) * np.eye(A.nrows()), K.precondition_tau(a))
        for m in degrees:
            R_ = np.eye(A.nrows()) - Af / float(b)
            P, term = np.zeros_like(R_), np.eye(A.nrows())
            for _ in range(m):
                P += term
                term = term @ R_
            Xf = (P / float(b)) @ Cf.T
            S = K.inverse_residual_form(B, k, a, exact(Xf))
            pre = K.certify_lower(A, a, K.precondition_tau(a), R=pre_R)
            st = form_status(S, 'S_X >= 0 (INVERSE_RESIDUAL)') if pre['status'] == 'CERTIFIED' else {'status': 'NOT_ELIGIBLE'}
            out['INVERSE_RESIDUAL'].append({'family': 'INVERSE_RESIDUAL', 'proposal': 'X = float P_m(A) C^T, P_m with parameter b (not a hypothesis)',
                'a': str(a), 'b_parameter': str(b), 'degree': m, 'X_proposal_sha256': array_sha256(Xf),
                'precondition': pre['status'], **st,
                'consumer': 'Zeta23.OPICARound4.ArithmeticFrontier.blockEnergy_nonneg_of_inverse_residual_certificate'})
        for m in tail_degrees:
            if cap != 'CERTIFIED':
                out['GEOMETRIC_TAIL'].append({'family': 'GEOMETRIC_TAIL', 'degree': m, 'status': 'NOT_ELIGIBLE', 'reason': 'A <= b I not certified'})
                continue
            S = K.geometric_tail_form(B, k, a, b, m)
            st = form_status(S, 'S_tail >= 0 (GEOMETRIC_TAIL, DERIVED sufficiency)')
            out['GEOMETRIC_TAIL'].append({'family': 'GEOMETRIC_TAIL', 'a': str(a), 'b': str(b), 'degree': m,
                                          'q_power_over_a': float((1 - a / b) ** m / a), **st})
    out['native_form'] = {'target_id': 'C1_CHECKPOINT_TOLERANCE', **certify(B, eps / 2)}
    out['interpretation'] = ('A failed or falsified family is a failure of that sufficient estimate; the native form fails only '
                             'with an exact negative vector of the full pencil.')
    return out


def high_support_test(M: arb_mat, W: arb_mat, C: arb_mat, weights: list[int], split_idx: int) -> dict:
    """Unshifted form on the exact legal subspace supported strictly above the split."""
    Cf = to_float(C)
    n = len(weights)
    Zf = kernel_basis(Cf, weights, n, start=split_idx)
    piv = [split_idx + p for p in pivots_for(Cf[:, split_idx:], n - split_idx)]
    Y = K.corrected_basis(exact(Zf), C, piv)
    F = Y.transpose() * M * Y
    G = Y.transpose() * W * Y
    ev, U = generalized_eig(sym(to_float(F)), sym(to_float(G)))
    rho = K.rayleigh(F, exact_col(U[:, 0]), G)
    return {'target_id': 'HIGH_SUPPORT_UNSHIFTED_SLICE', 'support': 'reduced indices >= %d (|n| > split)' % split_idx,
            'dimension': Y.ncols(), 'physical_rayleigh_upper': K.ball_record(rho),
            'floating_physical_extremes': [float(ev[0]), float(ev[-1])],
            'quarter_gap_law': {'statement': 'Q_p >= (1/4)||x||^2 on the high-support legal subspace (reconstructed reading; historical constant and support not imported)',
                                'status': 'FALSIFIED_BOUND' if K.certainly_negative(rho - K.q(Fraction(1, 4))) else 'NOT_REFUTED_BY_THIS_WITNESS'}}


F2 = Fraction
CAMPAIGN = {
    'archive_L2_even': dict(L=F2(2), parity='even', bits=192, bracket=True, margins=[F2(1, 2 ** 64)]),
    'archive_L2_odd': dict(L=F2(2), parity='odd', bits=192, bracket=True, margins=[F2(1, 2 ** 64)]),
    'archive_L9_4_even': dict(L=F2(9, 4), parity='even', bits=256, bracket=True, margins=[F2(1, 2 ** 100)]),
    'archive_L9_4_odd': dict(L=F2(9, 4), parity='odd', bits=256, bracket=True, margins=[F2(1, 2 ** 100)]),
    'archive_L5_2_even': dict(L=F2(5, 2), parity='even', bits=320, bracket=True, margins=[F2(1, 2 ** 146)]),
    'archive_L5_2_odd': dict(L=F2(5, 2), parity='odd', bits=320, bracket=True, margins=[F2(1, 2 ** 146)]),
    'L4_even': dict(L=F2(4), parity='even', bits=192, eps_list=[F2(1, 2), F2(1, 1024)], split=128),
    'L4_odd': dict(L=F2(4), parity='odd', bits=192, eps_list=[F2(1, 2), F2(1, 1024)], split=128),
    'L4_even_bracket': dict(L=F2(4), parity='even', bits=1024, bracket=True, high_support=False),
    'L4_odd_bracket': dict(L=F2(4), parity='odd', bits=1024, bracket=True, high_support=False),
    'L5_even': dict(L=F2(5), parity='even', bits=192, eps_list=[F2(1, 3), F2(1, 1024)], split=312),
    'L5_odd': dict(L=F2(5), parity='odd', bits=192, eps_list=[F2(1, 3), F2(1, 1024)], split=312),
    'EH6_L6_even': dict(L=F2(6), parity='even', bits=192, eps_list=[F2(1, 4)], split=648),
    'EH6_L6_odd': dict(L=F2(6), parity='odd', bits=192, eps_list=[F2(1, 4)], split=648),
}


def run_campaign(out_dir: Path, names: list[str]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    for name in names:
        rec = slice_run(**CAMPAIGN[name])
        rec['campaign_entry'] = name
        (out_dir / (name + '.json')).write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8')
        print(json.dumps({'entry': name, 'certificates': [c['status'] for c in rec['endpoint_certificates']],
                          'seconds': rec['seconds']}), flush=True)


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('--campaign', required=True, help='comma-separated campaign entries, or "all"')
    p.add_argument('--out-dir', type=Path, required=True)
    a = p.parse_args(argv)
    run_campaign(a.out_dir, list(CAMPAIGN) if a.campaign == 'all' else a.campaign.split(','))
    return 0


if __name__ == '__main__':
    sys.exit(main())
