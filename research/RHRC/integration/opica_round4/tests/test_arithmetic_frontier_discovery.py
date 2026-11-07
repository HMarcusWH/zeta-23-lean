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
except ImportError:
    NS = None


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
