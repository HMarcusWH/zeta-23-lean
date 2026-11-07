"""Optional discovery-layer controls for the numpy engine (not an acceptance test).

The engine ``native_slice.py`` proposes bases, factors, inverse actions and
witnesses with numpy; acceptance is decided by ``certificates.py`` and is
tested without numpy in ``test_arithmetic_frontier_acceptance.py`` and
``test_arithmetic_frontier_native.py``. This module is not wired into a CI lane
because numpy is not in the hash-locked environment; it reports skips there by
design. RH and Step 4 remain OPEN.
"""
from fractions import Fraction
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1] / 'arithmetic_frontier'
try:
    import numpy as np  # noqa: F401
    _spec = importlib.util.spec_from_file_location('_frontier_native_slice_discovery', ROOT / 'native_slice.py')
    NS = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(NS)
    NB = importlib.util.module_from_spec(importlib.util.spec_from_file_location('_frontier_nearband_discovery', ROOT / 'nearband_bound.py'))
    NB.__spec__.loader.exec_module(NB)
except ImportError:
    NS = NB = None


@unittest.skipIf(NS is None, 'DISCOVERY_LAYER_ONLY: numpy is not installed')
class DiscoveryEngineTests(unittest.TestCase):
    def test_small_state_run_uses_kernel_statuses(self):
        rec = NS.slice_run(Fraction(2), 'even', bits=192, bracket=True,
                           margins=[Fraction(1, 2 ** 64), Fraction(1, 2 ** 50)], high_support=False)
        self.assertEqual([c['status'] for c in rec['endpoint_certificates']], ['CERTIFIED', 'FALSIFIED_BOUND'])
        self.assertEqual(rec['bottom_bracket']['status'], 'BRACKETED')
        self.assertEqual(rec['state']['dimension'], 13)
        self.assertEqual(rec['basis']['full_gram_certificate']['status'], 'CERTIFIED')

    def test_block_tests_on_a_planted_pencil(self):
        q = NS.K.q
        F = NS.arb_mat([[q('1/2'), q(0), q('1/2')], [q(0), q('1/100'), q(0)], [q('1/2'), q(0), q(1)]])
        G = NS.K.identity(3)
        out = NS.block_tests(F, G, 1, Fraction(1, 10 ** 6), (1, 8), (8,))
        self.assertEqual(out['native_form']['status'], 'CERTIFIED')
        self.assertEqual(out['SCALAR_GAP']['status'], 'FALSIFIED_BOUND')
        self.assertTrue(all(r['status'] != 'FALSIFIED_BOUND' or r.get('witness_value') for r in out['INVERSE_RESIDUAL']))

    def test_dyadic_below_is_exact_for_tiny_values(self):
        x = Fraction(3, 2 ** 900)
        self.assertEqual(NS.dyadic_below(x), Fraction(1, 2 ** 899))


if __name__ == '__main__':
    unittest.main()


@unittest.skipIf(NB is None, 'DISCOVERY_LAYER_ONLY: numpy is not installed')
class NearBandDiscoveryTests(unittest.TestCase):
    def test_projector_free_bound_dominates_the_exact_projection(self):
        rng = np.random.default_rng(7)
        Q, _ = np.linalg.qr(rng.standard_normal((6, 6)))
        lam = np.array([0.5 + 1e-7, 0.5 + 3e-7, 0.9, 2.0, 4.0, 6.0])
        A = NS.sym(Q @ np.diag(lam) @ Q.T)
        C = rng.standard_normal((2, 6)) * 1e-3
        D = np.eye(2)
        B = NS.exact(np.block([[D, C], [C.T, A]]))
        out = NB.nearband_bounds(B, 2, Fraction(1, 2), offsets=(Fraction(1, 10 ** 6), Fraction(1, 10 ** 4)))
        for row in out['rows']:
            s = float(Fraction(row['s']))
            CU = NS.to_float(NS.blocks(B, 2)[1]) @ Q
            exact = float((CU[:, lam <= s] ** 2).sum())
            self.assertGreaterEqual(float(row['certified_trace_upper']), exact)
            self.assertEqual(row['certified_lambda_max_upper']['status'], 'CERTIFIED')

    def test_mode_transform_reproduces_the_native_pole_channel(self):
        cal = NB.pole_calibration()
        self.assertLess(max(cal['relative_max_error'].values()), 1e-12)
