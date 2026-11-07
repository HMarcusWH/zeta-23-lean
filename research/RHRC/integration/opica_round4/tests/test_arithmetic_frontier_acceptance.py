"""Mandatory countercontrols for the frontier acceptance kernel (Increment 2B).

Floating-point free and without optional skips: every acceptance or
falsification path of ``arithmetic_frontier/certificates.py`` is exercised in
the hash-locked CI environment. The review's nine miniature controls are the
specification; these tests run against the repaired repository functions.
RH and Step 4 remain OPEN.
"""
from fractions import Fraction
import importlib.util
from pathlib import Path
import unittest

from flint import arb, arb_mat, ctx

ROOT = Path(__file__).resolve().parents[1] / 'arithmetic_frontier'
_spec = importlib.util.spec_from_file_location('_frontier_certificates', ROOT / 'certificates.py')
K = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(K)
E = K.exact_matrix
V = K.exact_vector


class StatusSemanticsTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 128

    def test_equality_at_a_non_strict_bound_is_never_falsified(self):
        A = E([[1]])
        v = V([1])
        self.assertEqual(K.refute_lower(A, 1, v)['status'], 'NOT_REFUTED_BY_THIS_WITNESS')
        self.assertEqual(K.refute_upper(A, 1, v)['status'], 'NOT_REFUTED_BY_THIS_WITNESS')
        self.assertNotEqual(K.certify_lower(A, 1, Fraction(1, 10 ** 6))['status'], 'FALSIFIED_BOUND')

    def test_violations_need_a_certified_negative_witness(self):
        A = E([[1, 0], [0, Fraction(1, 2)]])
        self.assertEqual(K.refute_lower(A, Fraction(3, 4), V([0, 1]))['status'], 'FALSIFIED_BOUND')
        self.assertEqual(K.refute_lower(A, Fraction(3, 4), V([1, 0]))['status'], 'NOT_REFUTED_BY_THIS_WITNESS')
        self.assertEqual(K.refute_upper(A, Fraction(3, 4), V([1, 0]))['status'], 'FALSIFIED_BOUND')

    def test_failed_factorization_is_unknown_not_falsified(self):
        out = K.certify_shifted(E([[1, 0], [0, Fraction(-1, 10 ** 30)]]), Fraction(1, 10 ** 40))
        self.assertEqual(out['status'], 'UNKNOWN_PRECISION')


class ShiftPreconditionTests(unittest.TestCase):
    def test_review_negative_tau_control_is_rejected(self):
        # A = [-1], tau = -2, R = [1]: zero residual, yet A is negative.
        with self.assertRaises(K.InvalidCertificateInput):
            K.certify_shifted(E([[-1]]), -2, E([[1]]))

    def test_zero_tau_is_rejected(self):
        with self.assertRaises(K.InvalidCertificateInput):
            K.certify_shifted(E([[1]]), 0)

    def test_tiny_negative_refused_tiny_positive_accepted(self):
        tiny = Fraction(1, 10 ** 30)
        self.assertNotEqual(K.certify_shifted(E([[1, 0], [0, -tiny]]), tiny / 10)['status'], 'CERTIFIED')
        self.assertEqual(K.certify_shifted(E([[1, 0], [0, tiny]]), tiny / 10)['status'], 'CERTIFIED')
        self.assertNotEqual(K.certify_ldl(E([[1, 0], [0, -tiny]]))['status'], 'CERTIFIED')
        self.assertEqual(K.certify_ldl(E([[1, 0], [0, tiny]]))['status'], 'CERTIFIED')

    def test_nonsymmetric_input_is_rejected_by_every_reader(self):
        A = E([[1, 5], [0, 1]])
        for fn in (lambda: K.certify_ldl(A), lambda: K.certify_shifted(A, Fraction(1, 2)), lambda: K.certify_block_ldl(A, 1)):
            with self.assertRaises(K.InvalidCertificateInput):
                fn()

    def test_non_square_and_wrong_factor_dimensions(self):
        with self.assertRaises(K.InvalidCertificateInput):
            K.certify_shifted(arb_mat(2, 3), Fraction(1, 2))
        with self.assertRaises(K.InvalidCertificateInput):
            K.certify_shifted(E([[2, 0], [0, 2]]), Fraction(1, 2), E([[1]]))

    def test_inexact_factor_proposal_is_rejected(self):
        with self.assertRaises(K.InvalidCertificateInput):
            K.certify_shifted(E([[2]]), Fraction(1, 2), arb_mat([[arb(1, 1e-3)]]))

    def test_zero_dimensional_complement_is_explicit(self):
        out = K.certify_shifted(arb_mat(0, 0), Fraction(1, 2))
        self.assertTrue(out['vacuous'])

    def test_block_schur_matches_scalar_ldl(self):
        A = E([[4, 1, 0, 0], [1, 3, 1, 0], [0, 1, 2, 1], [0, 0, 1, 2]])
        self.assertEqual(K.certify_block_ldl(A, 2)['status'], 'CERTIFIED')
        Bad = E([[1, 2, 0], [2, 1, 0], [0, 0, 1]])
        self.assertNotEqual(K.certify_block_ldl(Bad, 1)['status'], 'CERTIFIED')


class EndpointAndNormTests(unittest.TestCase):
    def test_review_endpoint_control_is_enclosed(self):
        ctx.prec = 128
        m = Fraction(-1) + Fraction(1, 2 ** 54)
        r = Fraction(1) - Fraction(1, 2 ** 55)
        x = arb(K.q(m), K.q(r).mid())
        lo, hi = K.endpoints(x)
        self.assertGreaterEqual(hi, m + r)       # = 2^-55, never underestimated
        self.assertLessEqual(lo, m - r)
        self.assertEqual(K.exact_str(Fraction(3, 8)), '3*2^-3')

    def test_rayleigh_uses_the_enclosed_norm_of_the_given_gram(self):
        A = E([[2, 0], [0, 4]])
        v = V([1, 1])
        self.assertTrue(K.rayleigh(A, v).overlaps(K.q(3)))
        G = E([[1, 0], [0, 3]])
        self.assertTrue(K.rayleigh(A, v, G).overlaps(K.q(Fraction(6, 4))))
        with self.assertRaises(K.InvalidCertificateInput):
            K.rayleigh(A, V([0, 0]))

    def test_inexact_witness_is_rejected(self):
        with self.assertRaises(K.InvalidCertificateInput):
            K.quadratic(E([[1]]), arb_mat([[arb(1, 1e-9)]]))

    def test_non_finite_proposals_are_rejected(self):
        for bad in (float('nan'), float('inf')):
            with self.assertRaises(K.InvalidCertificateInput):
                E([[bad]])


class CarrierAndMetricTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 128

    def test_corrected_basis_is_in_the_kernel_and_pivots_are_certified(self):
        C = E([[1, 1, 1, 1], [0, 1, 2, 3]])
        Z = E([[1.0, 0.0], [0.0, 1.0], [0.5, 0.25], [0.0, 0.0]])
        Y = K.corrected_basis(Z, C, [2, 3])
        self.assertTrue(K.in_kernel(C, Y))
        with self.assertRaises(K.InvalidCertificateInput):
            K.corrected_basis(Z, E([[1, 1, 1, 1], [2, 2, 2, 2]]), [2, 3])   # singular pivot block
        with self.assertRaises(K.InvalidCertificateInput):
            K.corrected_basis(Z, C, [2, 2])

    def test_perturbed_correction_is_detected(self):
        C = E([[1, 1, 1, 1], [0, 1, 2, 3]])
        Y = K.corrected_basis(E([[1.0, 0.0], [0.0, 1.0], [0.0, 0.0], [0.0, 0.0]]), C, [2, 3])
        rows = Y.tolist()
        rows[0][0] = rows[0][0] + K.q(Fraction(1, 1000))
        self.assertFalse(K.in_kernel(C, arb_mat(rows)))

    def test_dropping_gram_cross_blocks_changes_the_physical_claim(self):
        F = E([[1, 0], [0, 1]])
        G = E([[1, Fraction(9, 10)], [Fraction(9, 10), 1]])
        Gdrop = E([[1, 0], [0, 1]])
        m = Fraction(9, 10)
        self.assertEqual(K.refute_lower(F, m, V([1, 1]), G)['status'], 'FALSIFIED_BOUND')
        self.assertEqual(K.certify_lower(F, m, Fraction(1, 20), Gdrop)['status'], 'CERTIFIED')

    def test_wrong_cutoff_and_altered_prime_weights_are_rejected(self):
        K.validate_state(4, 256, 54, [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53])
        with self.assertRaises(K.InvalidCertificateInput):
            K.validate_state(4, 255, 54, [])
        with self.assertRaises(K.InvalidCertificateInput):
            K.validate_state(4, 256, 54, [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 53])
        with self.assertRaises(K.InvalidCertificateInput):
            K.validate_state(4, 256, 55, [])


class CertificateFamilyTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 128
        # coupling only to the stiff direction of A: positive pencil, refuted scalar gap
        self.B = E([[Fraction(1, 2), 0, Fraction(1, 2)], [0, Fraction(1, 100), 0], [Fraction(1, 2), 0, 1]])

    def test_three_families_are_distinct_sufficient_inequalities(self):
        B, k = self.B, 1
        self.assertEqual(K.certify_ldl(B)['status'], 'CERTIFIED')
        self.assertNotEqual(K.family_scalar_gap(B, k, Fraction(1, 200), Fraction(1, 10 ** 6))['status'], 'CERTIFIED')
        refute = K.refute_scalar_gap_for_all(B, k, V([1, 0]), V([1]))
        self.assertEqual(refute['status'], 'FALSIFIED_BOUND')
        X = E([[0.0], [0.5]])  # exact proposal of A^-1 C^T
        self.assertEqual(K.family_inverse_residual(B, k, Fraction(1, 200), X, Fraction(1, 10 ** 6))['status'], 'CERTIFIED')
        tail = K.family_geometric_tail(B, k, Fraction(1, 200), Fraction(2), 8, Fraction(1, 10 ** 6))
        self.assertIn(tail['status'], ('CERTIFIED', 'UNKNOWN_PRECISION'))
        self.assertEqual(tail['family'], 'GEOMETRIC_TAIL')

    def test_geometric_tail_needs_a_certified_upper_bound(self):
        out = K.family_geometric_tail(self.B, 1, Fraction(1, 200), Fraction(1, 2), 4, Fraction(1, 10 ** 6))
        self.assertEqual(out['status'], 'NOT_ELIGIBLE')

    def test_exact_polynomial_residual_identity(self):
        A = E([[Fraction(1, 2), 0], [0, Fraction(3, 2)]])
        b, m = Fraction(2), 5
        P = K.polynomial_action(A, b, m)
        T = K.identity(2) - A * (1 / K.q(b))
        Tm = K.identity(2)
        for _ in range(m):
            Tm = Tm * T
        diff = K.identity(2) - A * P - Tm
        self.assertTrue(all(diff[i, j].contains(0) for i in range(2) for j in range(2)))

    def test_altered_inverse_action_never_certifies_a_negative_pencil(self):
        Bneg = E([[Fraction(1, 5), Fraction(1, 20)], [Fraction(1, 20), Fraction(1, 100)]])
        for x in (0.0, 5.0, 4.9, 100.0):
            out = K.family_inverse_residual(Bneg, 1, Fraction(1, 200), E([[x]]), Fraction(1, 10 ** 9))
            self.assertNotEqual(out['status'], 'CERTIFIED')

    def test_hashes_bind_exact_enclosures(self):
        a = E([[1, 2], [2, 1]])
        b = E([[1, 2], [2, Fraction(1) + Fraction(1, 2 ** 60)]])
        self.assertNotEqual(K.enclosure_sha256(a), K.enclosure_sha256(b))


if __name__ == '__main__':
    unittest.main()
