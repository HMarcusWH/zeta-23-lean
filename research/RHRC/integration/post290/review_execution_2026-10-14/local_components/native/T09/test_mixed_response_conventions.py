"""Finite exact binary/Gaussian controls, supplementary to the Lean identities.

These test algebraic signs, conjugation, and both shifts.  They do not replace
continuous Fourier analysis, the explicit formula, or actual prime coefficients.
"""
import unittest


def value(f, x):
    return f.get(x, 0j)


def correlation(f, v, a):
    return sum(value(f, x + a) * z.conjugate() for x, z in v.items())


class MixedResponseConventions(unittest.TestCase):
    def setUp(self):
        self.f = {-2: 1 + 2j, -1: -1 + 1j, 0: 2 - 1j, 1: 3 + 0j}
        self.v = {-1: 2 - 1j, 0: 1 + 3j, 1: -2 + 1j, 2: 1 - 2j}

    def test_both_prime_translations_and_mixed_orientation(self):
        coefficients = {1: 2, 2: 3}
        physical = sum(sum(c * (value(self.f, x - a) + value(self.f, x + a))
                           for a, c in coefficients.items()) * z.conjugate()
                       for x, z in self.v.items())
        expected = sum(c * (correlation(self.f, self.v, a) + correlation(self.f, self.v, -a))
                       for a, c in coefficients.items())
        self.assertEqual(physical, expected)
        self.assertNotEqual(physical.imag, 0)
        self.assertNotEqual(physical, expected.conjugate())
        omitted_history = sum(c * correlation(self.f, self.v, a) for a, c in coefficients.items())
        self.assertNotEqual(physical, omitted_history)
        self.assertNotEqual(physical, 2 * expected)

    def test_opposite_pole_arguments(self):
        def moment(f, sign):
            return sum(2 ** (sign * x) * z for x, z in f.items())

        minus_f, plus_f = moment(self.f, -1), moment(self.f, 1)
        physical = sum((2 ** x * minus_f + 2 ** (-x) * plus_f) * z.conjugate()
                       for x, z in self.v.items())
        expected = (minus_f * moment(self.v, 1).conjugate() +
                    plus_f * moment(self.v, -1).conjugate())
        wrong = (minus_f * moment(self.v, -1).conjugate() +
                 plus_f * moment(self.v, 1).conjugate())
        self.assertEqual(physical, expected)
        self.assertNotEqual(physical, wrong)

    def test_plus_transform_minus_inverse_and_normalization(self):
        # Fourth roots of unity and division by four are exact in binary.
        f = [1 + 2j, 3 - 1j, -2 + 1j, 1 - 3j]
        v = [2 - 1j, -1 + 2j, 4 + 1j, 2 + 0j]
        gamma = [2, 3, 5, 7]
        transform = lambda h: [sum(h[x] * (1j) ** (k * x) for x in range(4)) for k in range(4)]
        F, V = transform(f), transform(v)
        response = [sum(gamma[k] * F[k] * (1j) ** (-k * x) for k in range(4)) / 4
                    for x in range(4)]
        physical = sum(response[x] * v[x].conjugate() for x in range(4))
        spectral = sum(gamma[k] * F[k] * V[k].conjugate() for k in range(4)) / 4
        self.assertEqual(physical, spectral)
        self.assertNotEqual(physical, 4 * spectral)
        wrong_response = [sum(gamma[k] * F[k] * (1j) ** (k * x) for k in range(4)) / 4
                          for x in range(4)]
        self.assertNotEqual(physical, sum(wrong_response[x] * v[x].conjugate() for x in range(4)))


if __name__ == "__main__":
    unittest.main()
