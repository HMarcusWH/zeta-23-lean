"""Arithmetic-frontier native slices: independent checks and evidence binding (CI).

Floating-point free and without optional skips. It uses the shared numpy-free
source assembly ``native_source.py``, the acceptance kernel ``certificates.py``
and the independent checker ``independent_check.py``. It re-certifies the
archived small-aperture statements, reconstructs a small checkpoint on the
large-state path, and binds every recorded result to the exact producer bytes:

* Increment 2 records to the preserved version-1 producer in
  ``evidence/increment2/producer/`` (history, superseded acceptance logic);
* Increment 2B records to the current engine, source module and kernel;
* level-3 reconstructions to the checker, source module and kernel.

A hash check certifies byte identity only; the decisive inequalities are
recomputed only where a test says so. Numpy discovery controls live in
``test_arithmetic_frontier_discovery.py`` and are not acceptance tests.
RH and Step 4 remain OPEN.
"""
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1] / 'arithmetic_frontier'
EV2 = ROOT / 'evidence' / 'increment2'
EV2B = ROOT / 'evidence' / 'increment2b'
EV3C = ROOT / 'evidence' / 'increment3c'


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


IC = load('_frontier_independent_check_ci', ROOT / 'independent_check.py')
SRC = load('_frontier_native_source_ci', ROOT / 'native_source.py')
K = load('_frontier_certificates_ci', ROOT / 'certificates.py')


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_from_str(s: str) -> Fraction:
    if '*2^' in s:
        m, e = s.split('*2^')
        e = int(e)
        return Fraction(int(m)) * (Fraction(2) ** e if e >= 0 else Fraction(1, 2 ** (-e)))
    return Fraction(s)


class SourceAssemblyTests(unittest.TestCase):
    def test_vectorized_entries_match_the_direct_backend(self):
        st = SRC.NativeState(Fraction(5, 2), K=4, bits=128)
        ref = st.backend.canonical_source_matrix(st.L, 4, st.Q)
        for r, n in enumerate(range(-4, 5)):
            for c, m in enumerate(range(-4, 5)):
                self.assertTrue(st.entry(n, m).overlaps(ref[r, c]), (n, m))

    def test_parity_reduction_is_exact_with_physical_weights(self):
        st = SRC.NativeState(Fraction(5, 2), K=4, bits=128)
        ref = st.backend.canonical_source_matrix(st.L, 4, st.Q)
        z = [Fraction(3, 8), Fraction(-1, 4), Fraction(5, 16), Fraction(1, 8), Fraction(-3, 4)]  # exact dyadic witnesses
        for parity in ('even', 'odd'):
            E, w = st.reduced(parity)
            zz = z[:E.nrows()]
            x = [zz[abs(n)] if parity == 'even' else (Fraction(1 if n > 0 else -1) * zz[abs(n) - 1] if n else Fraction(0))
                 for n in range(-4, 5)]
            Z, X = K.exact_vector(zz), K.exact_vector(x)
            self.assertTrue(K.quadratic(E, Z).overlaps(K.quadratic(ref, X)))
            self.assertEqual(sum(v * v for v in x), sum(w[i] * zz[i] ** 2 for i in range(len(zz))))

    def test_slice_equations_are_the_lean_moments(self):
        st = SRC.NativeState(Fraction(2), K=6, bits=128)
        for parity, k in (('even', [0, 2, 4]), ('odd', [1, 3, 5])):
            C = st.constraints(parity)
            Y = IC.elimination_basis_on(C, IC.spread_pivots(C.ncols(), C.nrows()))
            self.assertEqual(Y.ncols(), 6 - 3 if parity == 'even' else 6 - 4)
            self.assertTrue(K.in_kernel(C, Y))

    def test_quartic_cutoff_prime_cell_and_precision_floor(self):
        self.assertEqual([SRC.quartic_cutoff(Fraction(x)) for x in (2, Fraction(9, 4), Fraction(5, 2), 4, 5, 6, 7)],
                         [16, 26, 40, 256, 625, 1296, 2401])
        self.assertEqual([p for p, _ in SRC.prime_atoms(12)], [2, 3, 4, 5, 7, 8, 9, 11])
        with self.assertRaises(ValueError):
            SRC.NativeState(Fraction(2), K=4, bits=64)


class IndependentCheckerTests(unittest.TestCase):
    def test_archived_point_statements_reproduced_independently(self):
        for L, margin, bits in ((Fraction(2), 2 ** 64, 192), (Fraction(9, 4), 2 ** 100, 256), (Fraction(5, 2), 2 ** 146, 512)):
            for parity in ('even', 'odd'):
                out = IC.check_margin(L, parity, Fraction(1, margin), bits)
                self.assertEqual(out['status'], 'CERTIFIED', (str(L), parity))
                self.assertEqual(out['dimension'], out['K'] - (3 if parity == 'even' else 4))

    def test_margin_above_the_bottom_is_falsified(self):
        self.assertEqual(IC.check_margin(Fraction(2), 'even', Fraction(1, 2 ** 50), 192)['status'], 'FALSIFIED_BOUND')

    def test_large_state_path_on_a_small_checkpoint(self):
        for parity in ('even', 'odd'):
            out = IC.reconstruct_checkpoint(Fraction(2), parity, Fraction(1, 2), bits=192, block=4)
            self.assertEqual(out['status'], 'CERTIFIED')
            self.assertEqual(out['assurance_level'], 'LEVEL_3_INDEPENDENT_BASIS_AND_CERTIFICATE_SHARED_SOURCE_ASSEMBLY')

    def test_large_state_path_refuses_a_negative_tolerance_claim(self):
        # tolerance -1/2 asks for a positive margin of 1/2, false at L = 2
        out = IC.reconstruct_checkpoint(Fraction(2), 'even', Fraction(-1, 2), bits=192, block=4)
        self.assertNotEqual(out['status'], 'CERTIFIED')


class Increment2HistoryTests(unittest.TestCase):
    """Version-1 records stay bound to the preserved version-1 producer bytes."""

    @classmethod
    def setUpClass(cls):
        cls.summary = json.loads((EV2 / 'SUMMARY.json').read_bytes())

    def test_records_are_bound_to_the_preserved_producer(self):
        producer = EV2 / 'producer' / 'native_slice.py'
        self.assertEqual(sha(producer), self.summary['engine_sha256'])
        for e in self.summary['records']:
            self.assertEqual(sha(EV2 / e['file']), e['sha256'])
            rec = json.loads((EV2 / e['file']).read_bytes())
            self.assertEqual(rec['source']['replay_module_sha256'], self.summary['engine_sha256'])
            self.assertEqual((rec['RH'], rec['Step4']), ('OPEN', 'OPEN'))
        for e in self.summary.get('supplementary', []):
            self.assertEqual(sha(EV2 / e['file']), e['sha256'])

    def test_corrections_cover_the_superseded_claims(self):
        corr = json.loads((EV2B / 'CORRECTIONS.json').read_bytes())
        ids = {c['id'] for c in corr['corrections']}
        for needed in ('R1', 'R2', 'R3', 'R4', 'R5', 'R6', 'R7', 'R8', 'R9'):
            self.assertIn(needed, ids)
        for c in corr['corrections']:
            for path in c.get('original_records', []):
                self.assertTrue((ROOT.parents[4] / path).is_file(), path)


class Increment3CDerivedTests(unittest.TestCase):
    """DERIVED statements of Increment 3C, recomputed exactly without floating point."""

    def test_even_power_majorant_of_the_spectral_indicator(self):
        lam = [Fraction(1, 8), Fraction(251, 1000), Fraction(3, 4), Fraction(3), Fraction(5)]
        A = K.identity(5, 0)
        for i, x in enumerate(lam):
            A[i, i] = K.q(x)
        Cm = K.exact_matrix([[Fraction(1, 2), Fraction(-3, 4), Fraction(1, 8), Fraction(5, 16), Fraction(1)],
                             [Fraction(1, 4), Fraction(1, 2), Fraction(-1), Fraction(3, 8), Fraction(-1, 2)]])
        b = Fraction(6)
        for s in (Fraction(1, 4), Fraction(1, 2), Fraction(4)):
            for k in (0, 3, 6):
                T = (K.identity(5, K.q(b)) - A) * (1 / K.q(b - s))
                for _ in range(k):
                    T = T * T
                tr = Cm * T * Cm.transpose()
                bound = tr[0, 0] + tr[1, 1]
                ind = sum(K.exact_value(Cm[r, i]) ** 2 for i, x0 in enumerate(lam) if x0 <= s for r in (0, 1))
                self.assertGreaterEqual(K.lower(bound), ind, (s, k))


class CorrectionsAddendumTests(unittest.TestCase):
    def test_addendum_scopes_high_support_and_records_the_genuine_failure(self):
        add = json.loads((ROOT / 'evidence' / 'increment3c' / 'CORRECTIONS_ADDENDUM.json').read_bytes())
        self.assertEqual((add['RH'], add['Step4']), ('OPEN', 'OPEN'))
        by_id = {c['id']: c for c in add['corrections']}
        self.assertEqual(set(by_id), {'R10', 'R11', 'R12'})
        self.assertIn('|n| > split', by_id['R10']['finding'])
        self.assertIn('does not falsify a historical certificate', by_id['R10']['repair'])
        self.assertIn('rhkg-compiler-receipt at 94cb6d8', by_id['R11']['finding'])
        # the increment2b corrections ledger stays bound to its summary hash
        summary = json.loads((EV2B / 'SUMMARY.json').read_bytes())
        self.assertEqual(sha(EV2B / 'CORRECTIONS.json'), summary['corrections']['sha256'])
        for node in self._high_support_nodes(summary):
            self.assertEqual(node['quarter_gap_law'], 'FALSIFIED_BOUND')

    @staticmethod
    def _high_support_nodes(summary):
        return [t['high_support_unshifted'] for t in summary['table'] if 'high_support_unshifted' in t]

    def test_high_support_records_name_their_exact_support(self):
        summary = json.loads((EV2B / 'SUMMARY.json').read_bytes())
        for e in summary['records']:
            rec = json.loads((EV2B / e['file']).read_bytes())
            hs = rec.get('high_support_unshifted')
            if hs is not None:
                self.assertIn('|n| > split', hs['support'])


class Increment2BEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.summary = json.loads((EV2B / 'SUMMARY.json').read_bytes())
        cls.records = {e['entry']: json.loads((EV2B / e['file']).read_bytes()) for e in cls.summary['records']}

    def test_records_bind_engine_source_kernel_and_backend(self):
        for e in self.summary['records']:
            self.assertEqual(sha(EV2B / e['file']), e['sha256'])
            src = self.records[e['entry']]['source']
            self.assertEqual(src['engine_sha256'], sha(ROOT / 'native_slice.py'))
            self.assertEqual(src['source_module_sha256'], sha(ROOT / 'native_source.py'))
            self.assertEqual(src['kernel_sha256'], sha(ROOT / 'certificates.py'))
            self.assertEqual(src['backend_sha256'], sha(SRC.BACKEND_PATH))

    def test_every_falsification_carries_a_negative_exact_witness(self):
        def walk(node):
            if isinstance(node, dict):
                if node.get('target_id') == 'HIGH_SUPPORT_UNSHIFTED_SLICE':
                    # The quarter-gap falsification is witnessed by the enclosed Rayleigh quotient of
                    # an exact vector (certainly positive Gram denominator): rho_hi < 1/4 is
                    # equivalent to a certified negative value of F - G/4 at that vector.
                    law = node['quarter_gap_law']
                    if law['status'] == 'FALSIFIED_BOUND':
                        self.assertLess(exact_from_str(node['physical_rayleigh_upper']['upper_exact']), Fraction(1, 4))
                    node = {k: v for k, v in node.items() if k != 'quarter_gap_law'}
                elif node.get('status') == 'FALSIFIED_BOUND':
                    wv = node.get('witness_value')
                    self.assertIsNotNone(wv, node)
                    self.assertLess(exact_from_str(wv['upper_exact']), 0, node)
                for v in node.values():
                    walk(v)
            elif isinstance(node, list):
                for v in node:
                    walk(v)
        for rec in self.records.values():
            walk(rec)

    def test_checkpoints_and_preserved_estimate_failures(self):
        for key, eps in (('L4', '1/2'), ('L5', '1/3'), ('EH6_L6', '1/4')):
            for parity in ('even', 'odd'):
                cert = self.records['%s_%s' % (key, parity)]['endpoint_certificates'][0]
                self.assertEqual((cert['tolerance'], cert['status']), (eps, 'CERTIFIED'))
        for parity in ('even', 'odd'):
            half, tiny = self.records['L4_' + parity]['block_tests']
            self.assertEqual(half['SCALAR_GAP']['status'], 'FALSIFIED_BOUND')
            self.assertEqual(tiny['SCALAR_GAP']['status'], 'FALSIFIED_BOUND')
            self.assertEqual(half['native_form']['status'], 'CERTIFIED')
            self.assertEqual(tiny['native_form']['status'], 'CERTIFIED')

    def test_positive_brackets_only_where_certified(self):
        for name, rec in self.records.items():
            br = rec.get('bottom_bracket')
            if br is not None and br['status'] == 'BRACKETED':
                self.assertEqual(br['margin_certificate']['status'], 'CERTIFIED')
            if name.startswith(('L5', 'EH6')):
                self.assertNotIn('bottom_bracket', rec)

    def test_independent_reconstructions(self):
        certified = set()
        for e in self.summary['independent_reconstructions']:
            rec = json.loads((EV2B / e['file']).read_bytes())
            self.assertEqual(sha(EV2B / e['file']), e['sha256'])
            self.assertEqual(rec['hashes']['checker_sha256'], sha(ROOT / 'independent_check.py'))
            self.assertEqual(rec['hashes']['native_source_sha256'], sha(ROOT / 'native_source.py'))
            self.assertEqual(rec['hashes']['kernel_sha256'], sha(ROOT / 'certificates.py'))
            self.assertEqual(rec['dimension'], rec['dimension_expected'])
            self.assertIn(rec['status'], ('CERTIFIED', 'UNKNOWN_PRECISION'))
            self.assertEqual(e['status'], rec['status'])
            if rec['status'] == 'CERTIFIED':
                certified.add((rec['L'], rec['parity']))
            else:
                self.assertEqual(e['role'], 'PRESERVED_FAILED_ATTEMPT')
        for L in ('4', '5', '6'):
            for parity in ('even', 'odd'):
                self.assertIn((L, parity), certified)
        self.assertIn('NOT_AN_RH_OR_STEP4_CLAIM', self.summary['scope'])


def _walk_falsifications(test, node):
    if isinstance(node, dict):
        if node.get('status') == 'FALSIFIED_BOUND' or node.get('pencil') == 'FALSIFIED_BOUND':
            wv = node.get('witness_value')
            test.assertIsNotNone(wv, node)
            test.assertLess(exact_from_str(wv['upper_exact']), 0, node)
        for v in node.values():
            _walk_falsifications(test, v)
    elif isinstance(node, list):
        for v in node:
            _walk_falsifications(test, v)


class Increment3CEvidenceTests(unittest.TestCase):
    """Projector-free near-band bounds and synthetic off-line controls (evidence/increment3c)."""

    @classmethod
    def setUpClass(cls):
        cls.summary = json.loads((EV3C / 'SUMMARY.json').read_bytes())
        cls.records = {e['entry']: json.loads((EV3C / e['file']).read_bytes()) for e in cls.summary['records']}

    def test_records_bind_tool_engine_source_kernel_and_backend(self):
        self.assertEqual((self.summary['RH'], self.summary['Step4']), ('OPEN', 'OPEN'))
        for e in self.summary['records']:
            self.assertEqual(sha(EV3C / e['file']), e['sha256'])
            h = self.records[e['entry']]['hashes']
            self.assertEqual(h['tool_sha256'], sha(ROOT / 'nearband_bound.py'))
            self.assertEqual(h['engine_sha256'], sha(ROOT / 'native_slice.py'))
            self.assertEqual(h['source_module_sha256'], sha(ROOT / 'native_source.py'))
            self.assertEqual(h['kernel_sha256'], sha(ROOT / 'certificates.py'))
            self.assertEqual(h['backend_sha256'], sha(SRC.BACKEND_PATH))
        cal = json.loads((EV3C / 'pole_calibration.json').read_bytes())
        self.assertEqual(cal['tool_sha256'], sha(ROOT / 'nearband_bound.py'))
        self.assertLess(max(cal['relative_max_error'].values()), 1e-12)

    def test_every_falsification_carries_a_negative_exact_witness(self):
        for rec in self.records.values():
            _walk_falsifications(self, rec)

    def test_projector_free_bounds_are_certified(self):
        for name, rec in self.records.items():
            for row in rec['nearband']['rows']:
                self.assertTrue(row['trace_ball']['upper_exact'], name)
                self.assertEqual(row['certified_lambda_max_upper']['status'], 'CERTIFIED', (name, row['s']))
                self.assertGreaterEqual(float(row['certified_trace_upper']), row['experimental_floating']['trace_M_s'] * (1 - 1e-9))

    def test_small_coupling_is_not_a_sign_criterion(self):
        for name, rec in self.records.items():
            controls = {c['control']: c for c in rec['synthetic']['controls']}
            s1 = controls['S1_low_block_rank_one']
            self.assertEqual((s1['pencil'], s1['C_and_A_blocks_identical']), ('FALSIFIED_BOUND', True), name)
            for c in controls.values():
                d = c.get('discrimination')
                if d is None:
                    continue
                self.assertEqual(d['native']['pencil']['status'], 'CERTIFIED', (name, c['control']))
                self.assertEqual(d['synthetic']['pencil']['status'], 'FALSIFIED_BOUND', (name, c['control']))


if __name__ == '__main__':
    unittest.main()
