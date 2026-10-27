from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import certificate_io as io
import controls
import finite_baseline as finite


class FiniteBaselineTests(unittest.TestCase):
    def setUp(self):
        self.fixture = io.load_strict_json(HERE/"fixtures/filtered_four_column.json", 65536)

    def test_exact_producer_and_independent_checker(self):
        result = finite.verify_filtered_baseline(self.fixture)
        self.assertEqual(result, finite.check_filtered_baseline(self.fixture))
        self.assertEqual(result["upper_square"], "315384568453197375401/4648566756368995059600")
        self.assertEqual(result["lower_square"], "4396431852289/49942416588800")
        self.assertEqual(result["mean"], "13/54")
        self.assertEqual(result["prefix_cap"], "41/54")
        self.assertFalse(result["analytic_dependencies_verified_here"])
        self.assertFalse(result["Lean_compiled_here"])

    def test_period_drift_and_general_exact_budget(self):
        with self.assertRaises(io.InvalidCertificate):
            finite.period_values(["1"])
        cells = finite.period_values(["1", "-1", "-1", "-2/3"])
        self.assertEqual(len(cells), 12)
        self.assertEqual(finite.periodic_energy_upper(cells, 48)["prefix_cap"], Fraction(41, 54))
        # Constant exact zero-mean oscillation: the tail rotation is recomputed.
        rotated = finite.periodic_energy_upper([Fraction(1), Fraction(0)], 3)
        self.assertEqual(rotated["mean"], Fraction(1, 2))
        self.assertGreaterEqual(rotated["prefix_cap"], 0)
        for cutoff in (True, 0, 100001):
            with self.subTest(cutoff=cutoff), self.assertRaises(io.InvalidCertificate):
                finite.periodic_energy_upper(cells, cutoff)

    def test_all_refusal_controls(self):
        cases = controls.finite_mutation_controls(self.fixture)
        self.assertEqual(len(cases), 21)
        self.assertTrue(all(x["passed"] and x["actual"] == "REJECT" for x in cases))
        self.assertTrue(all(x["evidence_class"] == "RUNTIME_NEGATIVE_FIXTURE" for x in cases))

    def test_finite_checker_does_not_reuse_producer(self):
        from unittest.mock import patch
        with patch.object(finite, "period_values", side_effect=RuntimeError("producer unavailable")), \
             patch.object(finite, "periodic_energy_upper", side_effect=RuntimeError("producer unavailable")):
            self.assertEqual(finite.check_filtered_baseline(self.fixture)["status"], "PASS_EXACT_FINITE_ARITHMETIC")

    def test_native_minor_arithmetic_has_no_analytic_authority(self):
        obj = io.load_strict_json(HERE/"fixtures/native_jump_minor.json", 65536)
        result = finite.verify_native_jump_minor(obj)
        self.assertEqual(result["minor_upper"], "-61/375000000000")
        self.assertFalse(result["analytic_bridge_verified"])
        obj["smooth_lower_coefficient"] = "0"
        with self.assertRaises(io.InvalidCertificate):
            finite.verify_native_jump_minor(obj)

    def test_scope_dispatch_keeps_unexecuted_controls_visible(self):
        result = controls.run_controls()
        self.assertEqual(result["status"], "PASS_EXECUTED_FINITE_CONTROLS_ONLY")
        self.assertEqual(len(result["executed_controls"]), 21)
        self.assertEqual(len(result["additional_mutation_designs"]), 32)
        self.assertTrue(all(r["execution"] == "NOT_CLAIMED_BY_THIS_SCOPED_RUN"
                            for r in result["additional_mutation_designs"]))
        self.assertFalse(result["full_control_acceptance"])
        self.assertFalse(result["full_core_accepted"])


if __name__ == "__main__":
    unittest.main()

