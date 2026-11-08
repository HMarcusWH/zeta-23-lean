"""Increment 5A: the coarse signed candidate (SG) on the actual native slices.

EXPERIMENTAL SIGNAL ONLY. Floating midpoints of the repository's Arb source are
used for every linear-algebra step; nothing here is an enclosure, a positivity
certificate or a growth law. RH and Step 4 remain OPEN.

Native objects (unchanged): the parity-reduced canonical source
``NativeState.reduced`` (pole - arch - prime, every prime power below e^L, the
literal quartic cutoff K = ceil(L^4)) and the Lean slice equations
``NativeState.constraints``. The reduced coordinates carry the physical
coefficient metric W = diag(1, 2, 2, ...) (even) or 2I (odd); everything below is
done in W-orthonormal coordinates y = W^(1/2) x, so V is a physical isometry.

The candidate is the supplier proposition (SG) of the 8 November paper
"Polynomial Geometry and Source Response": in one fixed parity, for all late L,

    ||z(L)|| <= C_z (1 + L)^a  and  min_i h_i(L) >= -C_h (1 + L)^b,

with J = V* D0 V (D0 = diag(n^2)), its eigenbasis v_i (geometry only, never an
energy eigenvector), H = V* E V, h_i = <v_i, H v_i>, w the unit leakage normal of
D0 off the slice and z = V* E w. With the native identities

    V* [D0, E] V = 0                       (NC, Lean M57),
    (1 - V V*) D0 V = w l*                 (rank-one leakage, Lean M57 functional form),
    [J, H] = z l* - l z*                   (M51 composed with NC),

one has H_ij = (z_i l_j - l_i z_j) / (theta_i - theta_j) off the diagonal and

    lambda_min(H) >= min_i h_i - 2 ||l|| ||z|| / g_J,      g_J = min gap of J.

This script measures every term at the given states, records the identity
residuals, and runs the matched controls that show what (SG) cannot get for free:
the scalar shift (z unchanged, every h_i moves), arbitrary real prime weights
(NC survives, so NC carries no arithmetic), and the two-by-two off-diagonal
countermodel (diagonal bounds alone do not bound lambda_min).
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
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


NS = _load('_frontier_native_slice_sg', 'native_slice.py')
SRC = NS.SRC

SCHEMA = 'OPICA4_ARITHMETIC_FRONTIER_SG_CANDIDATE_V1'
CAPS = {'RH': 'OPEN', 'Step4': 'OPEN', 'authority': 'EXPERIMENTAL_SIGNAL_FLOAT64_MIDPOINTS_NOT_CERTIFIED',
        'candidate_status': 'OPEN'}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def native_inputs(L: Fraction, parity: str, bits: int, prime_weights=None) -> dict:
    """Reduced source, metric and slice normals at one native state (float midpoints)."""
    st = SRC.NativeState(L, bits=bits)
    if prime_weights is not None:  # NOT native: arbitrary real weights per prime power
        from flint import arb
        logs = [(arb(q).log(), arb(prime_weights[i])) for i, (q, _) in enumerate(st.atoms)]
        pi, Lb = st.pi, st.L
        st.s, st.c = [], []
        for n in range(st.K + 1):
            ss, cc = arb(0), arb(0)
            for ell, w in logs:
                t = 2 * pi * n * ell / Lb
                ss += w * t.sin()
                cc += 2 * w * (1 - ell / Lb) * t.cos()
            st.s.append(ss / pi)
            st.c.append(cc)
    M, weights, ch = st.reduced(parity, with_channels=True)
    C = st.constraints(parity)
    idx = np.arange(0, st.K + 1) if parity == 'even' else np.arange(1, st.K + 1)
    return {'state': st, 'E': NS.to_float(M), 'arch': NS.to_float(ch['arch']), 'prime': NS.to_float(ch['prime']),
            'pole': NS.to_float(ch['pole']), 'W': np.array(weights, dtype=float), 'C': NS.to_float(C),
            'index': idx.astype(float)}


def geometry(data: dict) -> dict:
    """Physical isometry V of the slice, the leakage normal w and l = V* D0 w."""
    s = np.sqrt(data['W'])
    Ey = NS.sym(data['E'] / s[:, None] / s[None, :])
    D0 = data['index'] ** 2
    normals = (data['C'] / s[None, :]).T                      # columns: normals in y-coordinates
    Qn, _ = np.linalg.qr(normals)
    Qfull, _ = np.linalg.qr(np.hstack([Qn, np.eye(len(D0))]))
    V = Qfull[:, Qn.shape[1]:len(D0)]                          # orthonormal complement of the normals
    leak = D0[:, None] * V - V @ (V.T @ (D0[:, None] * V))      # (1 - V V*) D0 V
    U, sv, Wt = np.linalg.svd(leak, full_matrices=False)
    w = U[:, 0]
    ell = V.T @ (D0 * w)
    return {'Ey': Ey, 'D0': D0, 'V': V, 'w': w, 'ell': ell, 'leak_singular_values': sv[:4].tolist(),
            'normals_rank': int(np.linalg.matrix_rank(normals)), 'leak_rank_one_residual':
                float(np.linalg.norm(leak - np.outer(w, ell)) / max(np.linalg.norm(leak), 1e-300))}


def sg_measure(data: dict, geo: dict) -> dict:
    Ey, D0, V, w, ell = geo['Ey'], geo['D0'], geo['V'], geo['w'], geo['ell']
    H = NS.sym(V.T @ Ey @ V)
    J = NS.sym(V.T @ (D0[:, None] * V))
    z = V.T @ (Ey @ w)
    comm_ambient = D0[:, None] * Ey - Ey * D0[None, :]
    nc = V.T @ comm_ambient @ V
    comm = J @ H - H @ J
    rank2 = np.outer(z, ell) - np.outer(ell, z)
    theta, G = np.linalg.eigh(J)
    gaps = np.diff(theta)
    gJ = float(gaps.min())
    Hg = G.T @ H @ G
    zg, lg = G.T @ z, G.T @ ell
    h = np.diag(Hg).copy()
    off = Hg - np.diag(h)
    with np.errstate(divide='ignore', invalid='ignore'):
        pred = (np.outer(zg, lg) - np.outer(lg, zg)) / (theta[:, None] - theta[None, :])
    np.fill_diagonal(pred, 0.0)
    eig = np.linalg.eigvalsh(H)
    nz, nl = float(np.linalg.norm(z)), float(np.linalg.norm(ell))
    trace_identity = float(np.sum(h ** 2) + np.sum(pred ** 2))
    return {
        'slice_dimension': int(V.shape[1]),
        'nc_relative_residual': float(np.linalg.norm(nc) / max(np.linalg.norm(V.T @ (np.abs(comm_ambient)) @ V), 1e-300)),
        'nc_absolute_frobenius': float(np.linalg.norm(nc)),
        'ambient_commutator_frobenius': float(np.linalg.norm(comm_ambient)),
        'commutator_identity_relative_residual': float(np.linalg.norm(comm - rank2) / max(np.linalg.norm(comm), 1e-300)),
        'offdiagonal_reconstruction_relative_residual': float(np.linalg.norm(off - pred) / max(np.linalg.norm(off), 1e-300)),
        'leak_singular_values': geo['leak_singular_values'],
        'leak_rank_one_residual': geo['leak_rank_one_residual'],
        'geometry_min_gap': gJ, 'geometry_spectrum_range': [float(theta[0]), float(theta[-1])],
        'norm_z': nz, 'norm_l': nl, 'min_geometry_diagonal': float(h.min()),
        'argmin_geometry_diagonal_theta': float(theta[int(np.argmin(h))]),
        'max_geometry_diagonal': float(h.max()),
        'lambda_min_H': float(eig[0]), 'lambda_max_H': float(eig[-1]),
        'sg_lower_bound': float(h.min() - 2 * nl * nz / gJ),
        'sg_bound_slack': float(eig[0] - (h.min() - 2 * nl * nz / gJ)),
        'trace_H2': float(np.sum(H * H)), 'trace_identity_72': trace_identity,
        'trace_identity_relative_residual': float(abs(trace_identity - np.sum(H * H)) / np.sum(H * H)),
        'offdiagonal_operator_norm_bound_2lz_over_g': float(2 * nl * nz / gJ),
        'offdiagonal_actual_operator_norm': float(np.linalg.norm(off, 2)),
    }


def scalar_shift_control(data: dict, geo: dict, M: float = 1000.0) -> dict:
    """E - M I: z unchanged (w is orthogonal to the slice), every h_i moves by -M."""
    Ey = geo['Ey'] - M * np.eye(len(geo['D0']))
    z0 = geo['V'].T @ (geo['Ey'] @ geo['w'])
    z1 = geo['V'].T @ (Ey @ geo['w'])
    H0 = geo['V'].T @ geo['Ey'] @ geo['V']
    H1 = geo['V'].T @ Ey @ geo['V']
    return {'shift': M, 'z_change': float(np.linalg.norm(z1 - z0)),
            'diagonal_change': float(np.max(np.abs(np.diag(H1 - H0) + M))),
            'lambda_min_change': float(np.linalg.eigvalsh(NS.sym(H1))[0] - np.linalg.eigvalsh(NS.sym(H0))[0]),
            'conclusion': 'A response bound alone cannot control absolute energy (matched algebraic control).'}


def offdiagonal_countermodel(M: float = 10.0) -> dict:
    J = np.diag([0.0, 1.0]); ell = np.array([1.0, 1.0]); z = np.array([0.0, M])
    H = np.array([[0.0, M], [M, 0.0]])
    resid = float(np.linalg.norm(J @ H - H @ J - (np.outer(z, ell) - np.outer(ell, z))))
    return {'J': J.tolist(), 'ell': ell.tolist(), 'z': z.tolist(), 'H': H.tolist(), 'commutator_residual': resid,
            'diagonal': [0.0, 0.0], 'lambda_min': float(np.linalg.eigvalsh(H)[0]),
            'conclusion': 'Every h_i = 0 yet lambda_min = -M: diagonal lower bounds alone do not suffice.'}


def run_state(L: Fraction, parity: str, bits: int, controls: bool) -> dict:
    t0 = time.time()
    data = native_inputs(L, parity, bits)
    geo = geometry(data)
    row = {'L': str(L), 'parity': parity, 'K': data['state'].K, 'Q': data['state'].Q,
           'prime_powers': len(data['state'].atoms), 'bits': bits, **sg_measure(data, geo)}
    if controls:
        row['scalar_shift_control'] = scalar_shift_control(data, geo)
        rng = np.random.default_rng(20261108)
        weights = (rng.standard_normal(len(data['state'].atoms)) * 3.0).tolist()
        mod = native_inputs(L, parity, bits, prime_weights=weights)
        mgeo = geometry(mod)
        mrow = sg_measure(mod, mgeo)
        row['modified_prime_weights_control'] = {
            'label': 'NOT_ZETA: arbitrary real prime-power weights, seed 20261108, scale 3',
            'nc_relative_residual': mrow['nc_relative_residual'],
            'commutator_identity_relative_residual': mrow['commutator_identity_relative_residual'],
            'lambda_min_H': mrow['lambda_min_H'], 'norm_z': mrow['norm_z'],
            'min_geometry_diagonal': mrow['min_geometry_diagonal'],
            'conclusion': 'NC and the rank-two commutator survive arbitrary real weights; they carry no arithmetic.'}
    row['seconds'] = round(time.time() - t0, 3)
    return row


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--states', default='4:even,4:odd,5:even,5:odd,6:even,6:odd')
    ap.add_argument('--bits', type=int, default=128)
    ap.add_argument('--controls', action='store_true')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args(argv)
    rows = []
    for item in args.states.split(','):
        L, parity = item.split(':')
        rows.append(run_state(Fraction(L), parity, args.bits, args.controls))
        print(json.dumps({k: rows[-1][k] for k in ('L', 'parity', 'slice_dimension', 'geometry_min_gap', 'norm_z',
                                                   'min_geometry_diagonal', 'lambda_min_H', 'sg_lower_bound',
                                                   'nc_relative_residual', 'leak_rank_one_residual')}), flush=True)
    record = {'schema': SCHEMA, **CAPS, 'tool_sha256': sha256_file(Path(__file__)),
              'native_source_sha256': sha256_file(HERE / 'native_source.py'),
              'backend_sha256': sha256_file(SRC.BACKEND_PATH), 'numpy': np.__version__,
              'offdiagonal_countermodel': offdiagonal_countermodel(), 'states': rows}
    args.output.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    return 0


if __name__ == '__main__':
    sys.exit(main())
