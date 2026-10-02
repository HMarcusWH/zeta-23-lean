from __future__ import annotations

import sys
import unittest
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROUTE = HERE.parent
sys.path.insert(0, str(ROUTE))

import post280_saturation_frontier as sf


class SaturationFrontierTests(unittest.TestCase):
    def test_source_matrix_endpoints(self):
        for K in (2, 3):
            self.assertTrue(np.allclose(sf.source_matrix(0.0, K), 0.0, atol=1e-12))
            self.assertTrue(
                np.allclose(
                    sf.source_matrix(1.0, K),
                    2.0 * np.eye(2 * K + 1),
                    atol=1e-10,
                )
            )

    def test_boundary_flat_parity_bases(self):
        for K in (3, 4):
            ns = sf.centered(K)
            for parity in ("even", "odd"):
                U = sf.boundary_flat_parity_basis(K, parity)
                for p in range(3):
                    self.assertLess(float(np.max(np.abs((ns ** p) @ U))), 1e-9)

    def test_von_mangoldt_controls(self):
        self.assertGreater(sf.von_mangoldt_float(13), 0.0)
        self.assertGreater(sf.von_mangoldt_float(16), 0.0)
        self.assertEqual(sf.von_mangoldt_float(14), 0.0)
        self.assertEqual(sf.von_mangoldt_float(15), 0.0)
        self.assertEqual(sf.von_mangoldt_float(18), 0.0)

    def test_source_derivative_matches_finite_difference(self):
        K = 3
        omega = 0.37
        h = 1e-7
        fd = (sf.source_matrix(omega + h, K) - sf.source_matrix(omega - h, K)) / (2*h)
        self.assertTrue(np.allclose(fd, sf.source_matrix_prime(omega, K), rtol=2e-6, atol=2e-6))


if __name__ == "__main__":
    unittest.main()
