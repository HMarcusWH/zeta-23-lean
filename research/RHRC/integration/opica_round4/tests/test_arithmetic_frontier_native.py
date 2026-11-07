"""Arithmetic-frontier native-slice replay: independent checks and evidence binding.

The CI part is floating-point free: it uses the independent Arb checker
``independent_check.py`` (python-flint and sympy only, both hash-locked) and
the recorded campaign. It re-certifies the archived small-aperture point
statements, checks soundness controls, and binds every recorded result,
including every failed surrogate, to the engine and backend that produced it.

The replay engine ``native_slice.py`` needs numpy, which is not in the locked
CI environment. Its planted controls run only where numpy is installed and
are reported as skipped otherwise; the skip reason says so. RH and Step 4
remain OPEN.
"""
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1] / 'arithmetic_frontier'
EVIDENCE = ROOT / 'evidence' / 'increment2'


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


IC = load('_frontier_independent_check', ROOT / 'independent_check.py')
try:
    import numpy as np  # noqa: F401
    NS = load('_frontier_native_slice', ROOT / 'native_slice.py')
except ImportError:
    np = NS = None
DISPOSITIONS = ('CERTIFIED', 'FALSIFIED_BOUND', 'UNKNOWN_PRECISION', 'RESOURCE_STOP', 'NOT_ELIGIBLE')
LOCAL_ONLY = 'LOCAL_RESEARCH_ENGINE_ONLY: numpy is not in the hash-locked CI environment'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class IndependentCheckerTests(unittest.TestCase):
    def test_carrier_dimensions_and_exact_basis(self):
        for parity, dim in (('even', 13), ('odd', 12)):
            forms = IC.slice_forms(Fraction(2), parity, 128)
            self.assertEqual((forms['K'], forms['Q'], forms['dimension']), (16, 7, dim))
        self.assertEqual([IC.quartic_cutoff(Fraction(x)) for x in (2, Fraction(9, 4), Fraction(5, 2), 4, 5, 6)],
                         [16, 26, 40, 256, 625, 1296])

    def test_interval_ldl_refuses_indefinite_and_accepts_tiny_positive(self):
        tiny = IC.arb(1) / 10 ** 30
        self.assertFalse(IC.ldl_positive(IC.arb_mat([[1, 0], [0, -tiny]]))[0])
        self.assertTrue(IC.ldl_positive(IC.arb_mat([[1, 0], [0, tiny]]))[0])
        self.assertFalse(IC.ldl_positive(IC.arb_mat([[1, 1], [1, 1]]))[0])

    def test_archived_point_statements_reproduced_independently(self):
        for L, margin, bits in ((Fraction(2), 2 ** 64, 192), (Fraction(9, 4), 2 ** 100, 256), (Fraction(5, 2), 2 ** 146, 512)):
            for parity in ('even', 'odd'):
                out = IC.check_margin(L, parity, Fraction(1, margin), bits)
                self.assertEqual(out['status'], 'CERTIFIED', (str(L), parity))
                self.assertEqual(out['dimension'], out['K'] - (3 if parity == 'even' else 4))

    def test_margin_above_the_bottom_is_falsified(self):
        out = IC.check_margin(Fraction(2), 'even', Fraction(1, 2 ** 50), 192)
        self.assertEqual(out['status'], 'FALSIFIED_BOUND')

    def test_checker_agrees_with_recorded_engine_bracket(self):
        rec = json.loads((EVIDENCE / 'archive_L2_even.json').read_bytes())
        out = IC.check_margin(Fraction(2), 'even', Fraction(1, 2 ** 64), 192)
        engine = IC.arb(rec['bottom_bracket']['rayleigh_upper'])
        mine = IC.arb(out['rayleigh_upper'])
        self.assertTrue(abs(engine - mine) < engine / 10 ** 6)


@unittest.skipIf(NS is None, LOCAL_ONLY)
class EngineControlTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.st = NS.NativeState(Fraction(5, 2), K=4, bits=128)

    def test_vectorized_entries_match_repository_backend(self):
        st = self.st
        ref = st.backend.canonical_source_matrix(st.L, 4, st.Q)
        for r, n in enumerate(range(-4, 5)):
            for c, m in enumerate(range(-4, 5)):
                self.assertTrue(st.entry(n, m).overlaps(ref[r, c]), (n, m))

    def test_parity_reduction_is_exact_with_physical_weights(self):
        st = self.st
        ref = st.backend.canonical_source_matrix(st.L, 4, st.Q)
        rng = np.random.RandomState(7)
        for parity in ('even', 'odd'):
            E, w = st.reduced(parity)
            z = rng.randn(E.nrows())
            if parity == 'even':
                x = [z[abs(n)] for n in range(-4, 5)]
            else:
                x = [(np.sign(n) * z[abs(n) - 1] if n else 0.0) for n in range(-4, 5)]
            Z, X = NS.from_float(z.reshape(-1, 1)), NS.from_float(np.array(x).reshape(-1, 1))
            self.assertTrue((Z.transpose() * E * Z)[0, 0].overlaps((X.transpose() * ref * X)[0, 0]))
            self.assertAlmostEqual(sum(v * v for v in x), sum(w[i] * z[i] ** 2 for i in range(len(z))), places=12)

    def test_constraint_rows_are_the_lean_moments_and_pole_profiles(self):
        st = NS.NativeState(Fraction(2), K=6, bits=128)
        L, pi = st.L, st.pi
        for parity in ('even', 'odd'):
            C = NS.to_float(st.constraints(parity))
            Z = NS.kernel_basis(C, st.reduced(parity)[1], C.shape[1])
            v = Z @ np.random.RandomState(3).randn(Z.shape[1])
            full = {n: (v[abs(n)] if parity == 'even' else (np.sign(n) * v[abs(n) - 1] if n else 0.0)) for n in range(-6, 7)}
            moments = {k: sum(n ** k * full[n] for n in full) for k in range(6)}
            pe = sum(float(L.mid()) / float((L ** 2 + 16 * pi ** 2 * n * n).mid()) * full[n] for n in full)
            po = sum(float((4 * pi * n).mid()) / float((L ** 2 + 16 * pi ** 2 * n * n).mid()) * full[n] for n in full)
            zero = [0, 1, 2, 4] if parity == 'even' else [0, 1, 2, 3, 5]
            for k in zero:
                self.assertAlmostEqual(moments[k], 0.0, places=8)
            self.assertAlmostEqual(pe if parity == 'even' else po, 0.0, places=10)
            self.assertEqual(Z.shape[1], 6 - 3 if parity == 'even' else 6 - 4)

    def test_quartic_cutoff_and_prime_cell(self):
        self.assertEqual([NS.quartic_cutoff(Fraction(x)) for x in (2, Fraction(9, 4), Fraction(5, 2), 4, 5, 6)],
                         [16, 26, 40, 256, 625, 1296])
        self.assertEqual([q for q, _ in NS.prime_atoms(12)], [2, 3, 4, 5, 7, 8, 9, 11])
        with self.assertRaises(ValueError):
            NS.NativeState(Fraction(2), K=4, bits=64)

    def test_shifted_certificate_refuses_an_indefinite_matrix(self):
        A = NS.arb_mat([[1, 0], [0, NS.arb(-1) / 10 ** 30]])
        self.assertNotEqual(NS.certify_psd(A, Fraction(1, 10 ** 40))['status'], 'CERTIFIED')
        self.assertNotEqual(NS.certify_shifted(A, Fraction(1, 10 ** 40))['status'], 'CERTIFIED')
        B = NS.arb_mat([[1, 0], [0, NS.arb(1) / 10 ** 30]])
        self.assertEqual(NS.certify_shifted(B, Fraction(1, 10 ** 31))['status'], 'CERTIFIED')

    def test_margin_above_the_bottom_is_falsified_by_the_exact_vector(self):
        rec = NS.slice_run(Fraction(2), 'even', bits=192, bracket=True,
                           margins=[Fraction(1, 2 ** 64), Fraction(1, 2 ** 50)])
        statuses = [c['status'] for c in rec['endpoint_certificates']]
        self.assertEqual(statuses, ['CERTIFIED', 'FALSIFIED_BOUND'])
        self.assertEqual(rec['bottom_bracket']['status'], 'BRACKETED')
        self.assertEqual(rec['state']['dimension'], 13)
        self.assertTrue(rec['bottom_vector_budget']['pole'].startswith('[+/-'))

    def test_scalar_gap_failure_is_not_a_native_failure(self):
        q = lambda x: NS.rational_arb(Fraction(x))
        eps = Fraction(1, 10 ** 6)
        # one-dimensional A: the scalar gap is the exact Schur complement
        F = NS.arb_mat([[q('1/2'), q('1/20')], [q('1/20'), q('1/100')]])
        out = NS.block_test(F, NS.identity(2, 0), 1, eps, reported=None)
        self.assertEqual(out['native_form']['status'], 'CERTIFIED')
        self.assertEqual(out['polynomial']['status'], 'CERTIFIED')
        self.assertEqual(out['scalar_gap']['status'], 'NOT_REFUTED_BY_THIS_WITNESS')
        # coupling only to the stiff direction of A: positive form, refuted scalar gap
        F2 = NS.arb_mat([[q('1/2'), q(0), q('1/2')], [q(0), q('1/100'), q(0)], [q('1/2'), q(0), q(1)]])
        out2 = NS.block_test(F2, NS.identity(3, 0), 1, eps, reported=None)
        self.assertEqual(out2['scalar_gap']['status'], 'FALSIFIED_BOUND')
        self.assertEqual(out2['native_form']['status'], 'CERTIFIED')
        # an indefinite planted form is never certified
        F3 = NS.arb_mat([[q('1/5'), q('1/20')], [q('1/20'), q('1/100')]])
        out3 = NS.block_test(F3, NS.identity(2, 0), 1, eps, reported=None)
        self.assertNotEqual(out3['native_form']['status'], 'CERTIFIED')
        self.assertNotEqual(out3['polynomial']['status'], 'CERTIFIED')


class CampaignEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.summary = json.loads((EVIDENCE / 'SUMMARY.json').read_bytes())
        cls.records = {e['entry']: json.loads((EVIDENCE / e['file']).read_bytes()) for e in cls.summary['records']}

    def test_records_are_hash_bound_to_this_engine_and_backend(self):
        engine = sha(ROOT / 'native_slice.py')
        backend = sha(IC.BACKEND_PATH)
        self.assertEqual(self.summary['engine_sha256'], engine)
        for e in self.summary['records']:
            self.assertEqual(sha(EVIDENCE / e['file']), e['sha256'], e['file'])
            rec = self.records[e['entry']]
            self.assertEqual(rec['source']['replay_module_sha256'], engine)
            self.assertEqual(rec['source']['backend_sha256'], backend)
            self.assertEqual((rec['RH'], rec['Step4']), ('OPEN', 'OPEN'))
            self.assertEqual(rec['authority'], 'RESEARCH_CERTIFICATION_NOT_LEAN_AUTHORITY')
            self.assertEqual(rec['state']['dimension'], rec['state']['K'] - (3 if rec['state']['parity'] == 'even' else 4))

    def test_archived_point_statements_are_reproduced(self):
        for name, margin in (('archive_L2', 2 ** 64), ('archive_L9_4', 2 ** 100), ('archive_L5_2', 2 ** 146)):
            for parity in ('even', 'odd'):
                rec = self.records['%s_%s' % (name, parity)]
                self.assertEqual(rec['endpoint_certificates'][0]['margin'], str(Fraction(1, margin)))
                self.assertEqual(rec['endpoint_certificates'][0]['status'], 'CERTIFIED')
                self.assertEqual(rec['bottom_bracket']['status'], 'BRACKETED')

    def test_failed_surrogates_are_preserved(self):
        for parity in ('even', 'odd'):
            half, tiny = self.records['L4_' + parity]['block_tests']
            self.assertEqual([x['status'] for x in [half['scalar_gap'], tiny['scalar_gap']]], ['FALSIFIED_BOUND'] * 2)
            self.assertEqual(half['polynomial']['status'], 'CERTIFIED')
            self.assertEqual(half['high_block_bounds'][0]['a_le_A'], 'CERTIFIED')
            self.assertEqual(tiny['polynomial']['status'], 'FALSIFIED_BOUND')
            self.assertEqual(tiny['fixed_quarter_high_gap']['status'], 'FALSIFIED_BOUND')
            self.assertEqual(tiny['native_form']['status'], 'CERTIFIED')
            for b in self.records['L5_' + parity]['block_tests']:
                self.assertEqual(b['scalar_gap']['status'], 'FALSIFIED_BOUND')
                self.assertEqual(b['high_block_bounds'][0]['A_le_b'], 'FALSIFIED_BOUND')
                self.assertEqual(b['native_form']['status'], 'CERTIFIED')

    def test_checkpoints_are_tolerance_statements_only(self):
        for key, eps in (('L4', '1/2'), ('L5', '1/3'), ('EH6_L6', '1/4')):
            for parity in ('even', 'odd'):
                rec = self.records['%s_%s' % (key, parity)]
                cert = rec['endpoint_certificates'][0]
                self.assertEqual((cert['tolerance'], cert['status']), (eps, 'CERTIFIED'))
                for b in rec['budget_records']:
                    self.assertIn(b['disposition'], DISPOSITIONS)
                    self.assertEqual(b['state']['state_kind'], 'ACTUAL_STATE')
        self.assertIn('NOT_AN_RH_OR_STEP4_CLAIM', self.summary['scope'])


if __name__ == '__main__':
    unittest.main()
