"""Exact finite polynomial controls for the universal Lean proof's conventions."""
from fractions import Fraction as Q
from math import comb
import unittest


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    result = [Q(0)] * max(len(p), len(q))
    for i, a in enumerate(p):
        result[i] += a
    for i, a in enumerate(q):
        result[i] += a
    return trim(result)


def scale(c, p):
    return trim([c * a for a in p])


def mul(p, q):
    result = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return trim(result)


def deriv(p):
    return trim([Q(i) * p[i] for i in range(1, len(p))] or [Q(0)])


def primitive(p):
    return [Q(0)] + [a / (i + 1) for i, a in enumerate(p)]


def evaluate(p, x):
    result = Q(0)
    for a in reversed(p):
        result = a + x * result
    return result


def integrate(p, a, b):
    P = primitive(p)
    return evaluate(P, b) - evaluate(P, a)


def affine(p, c, d):
    result = [Q(0)]
    for i, a in enumerate(p):
        result = add(result, [a * comb(i, j) * c ** (i - j) * d ** j for j in range(i + 1)])
    return result


def power(p, n):
    result = [Q(1)]
    for _ in range(n):
        result = mul(result, p)
    return result


def periodic_primitives(count):
    result = [[Q(-1, 2), Q(1)]]
    for _ in range(count - 1):
        P = primitive(result[-1])
        result.append(add(P, [-integrate(P, Q(0), Q(1))]))
    return result


class FiniteOrderConventions(unittest.TestCase):
    def test_zero_mean_derivative_and_seams(self):
        kernels = periodic_primitives(7)
        self.assertEqual(kernels[0], [Q(-1, 2), Q(1)])
        self.assertEqual(kernels[1], [Q(1, 12), Q(-1, 2), Q(1, 2)])
        for index, P in enumerate(kernels):
            self.assertEqual(integrate(P, Q(0), Q(1)), 0)
            if index:
                self.assertEqual(deriv(P), kernels[index - 1])
                self.assertEqual(evaluate(P, Q(0)), evaluate(P, Q(1)))

    def test_finite_integer_summation_all_signs(self):
        # The hard extension of this polynomial has vanishing endpoint jets
        # through order 7; the test uses only orders 1 through 6.
        M = 3
        f = mul(power([Q(0), Q(1)], 8), power([Q(M), Q(-1)], 8))
        discrepancy = sum(evaluate(f, Q(k)) for k in range(M)) - integrate(f, Q(0), Q(M))
        self.assertNotEqual(discrepancy, 0)
        derivative = f
        for N, kernel in enumerate(periodic_primitives(6), start=1):
            derivative = deriv(derivative)
            cell_sum = sum(integrate(mul(affine(kernel, Q(-k), Q(1)), derivative),
                                     Q(k), Q(k + 1)) for k in range(M))
            self.assertEqual(discrepancy, (-1) ** (N + 1) * cell_sum)
            self.assertNotEqual(discrepancy, (-1) ** N * cell_sum)

    def test_actual_recurrence_chain_rule_model(self):
        # Compare independent u- and y-coordinate polynomial recurrences.
        t = Q(7, 3)
        A = [Q(2), Q(1), Q(-3), Q(2)]
        B = [Q(0)]
        y_profile = mul([Q(0), Q(1)], affine(A, t, Q(-1)))
        for N in range(6):
            bracket = add(mul([Q(0), Q(1)], affine(A, t, Q(-1))), affine(B, t, Q(-1)))
            self.assertEqual(y_profile, bracket)
            alpha = Q(N) + Q(1, 2)
            next_A = add(scale(-alpha, A), scale(Q(-1), deriv(A)))
            next_B = add(add(A, scale(-alpha, B)), scale(Q(-1), deriv(B)))
            y_profile = add(deriv(y_profile), scale(-alpha, y_profile))
            A, B = next_A, next_B


if __name__ == "__main__":
    unittest.main()
