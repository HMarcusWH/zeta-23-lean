"""Exact finite convention checks; these supplement, never replace, Lean.

The polynomial model uses Taylor coefficients for the actual formula's
nonvanishing R*J factor and a zero of multiplicity m.  No zeta-zero existence
or analytic continuation is inferred from this finite algebra.
"""
from fractions import Fraction as Q
from math import factorial
import unittest


def multiply(a, b):
    result = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def derivative(a):
    return [Q(i) * a[i] for i in range(1, len(a))]


class NativeTransformConventions(unittest.TestCase):
    def test_multiplicities_one_two_three(self):
        # Two independently nonconstant factors, with nonzero constant terms.
        rational_factor = [Q(2, 3), Q(5, 7), Q(11, 13)]
        source_factor = [Q(17, 19), Q(23, 29)]
        unit = multiply(rational_factor, source_factor)
        for m in (1, 2, 3):
            with self.subTest(m=m):
                zeta = [Q(0)] * m + [Q(31, 37), Q(41, 43)]
                kernel = multiply(rational_factor, zeta)
                input_jet = [-x for x in multiply(unit, derivative(zeta))]
                self.assertTrue(all(x == 0 for x in kernel[:m]))
                self.assertNotEqual(kernel[m], 0)
                self.assertTrue(all(x == 0 for x in input_jet[:m - 1]))
                self.assertNotEqual(input_jet[m - 1], 0)
                actual_derivative = factorial(m - 1) * input_jet[m - 1]
                actual_pairing = (-1) ** (m - 1) * actual_derivative
                zeta_derivative = factorial(m) * zeta[m]
                expected = (-1) ** m * unit[0] * zeta_derivative
                self.assertEqual(actual_pairing, expected)
                # An added factorial is already falsified for m=3.
                if m == 3:
                    self.assertNotEqual(actual_pairing, expected * factorial(m - 1))
                self.assertNotEqual(actual_pairing, -expected)

    def test_damping_and_conjugate_slot(self):
        # Exact real/imaginary pairs avoid floating-point tolerance.
        w = (Q(3, 8), Q(5, 11))
        epsilon = Q(1, 8)
        expected_point = (Q(1, 2), Q(5, 11))
        actual_point = (w[0] + epsilon, w[1])
        self.assertEqual(actual_point, expected_point)
        self.assertNotEqual((w[0] - epsilon, w[1]), expected_point)
        self.assertNotEqual((w[0] + epsilon, -w[1]), expected_point)
        # Conjugate-linear first slot conjugates the witness's conjugate w.
        witness_exponent = (-w[0], w[1])
        first_slot_conjugate = (witness_exponent[0], -witness_exponent[1])
        damped_exponent = (first_slot_conjugate[0] - epsilon, first_slot_conjugate[1])
        self.assertEqual(damped_exponent, (-expected_point[0], -expected_point[1]))

    def test_single_source_factor_and_exceptional_point(self):
        source_constant = Q(17, 19)
        self.assertNotEqual(source_constant, source_constant ** 2)
        # R(1/2)=0 while zeta(w+1/2) has a pole: substitution in a totalized
        # product would lose the actual kernel transform's residue value 1/2.
        w = Q(1, 2)
        rational_value = (w - Q(1, 2)) / ((w + Q(1, 2)) * (w + Q(3, 2)))
        self.assertEqual(rational_value, 0)
        self.assertNotEqual(rational_value * 0, Q(1, 2))


if __name__ == "__main__":
    unittest.main()
