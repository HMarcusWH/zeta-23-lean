from __future__ import annotations

from decimal import Decimal
import unittest

from interval_codec import DyadicInterval, IntervalCodecError


class IntervalCodecTests(unittest.TestCase):
    def test_one_third_is_outward_contained(self):
        x = Decimal(1) / Decimal(3)
        d = DyadicInterval.from_decimal_bounds(x, x, bits=80)
        self.assertTrue(d.contains(x))

    def test_near_zero_sign_is_recomputed(self):
        d = DyadicInterval.from_mid_rad("1e-40", "2e-40", bits=256)
        self.assertEqual(d.sign(), "CONTAINS_ZERO")

    def test_positive_and_negative(self):
        self.assertEqual(DyadicInterval.from_decimal_bounds("1e-20", "2e-20").sign(), "POSITIVE")
        self.assertEqual(DyadicInterval.from_decimal_bounds("-2e-20", "-1e-20").sign(), "NEGATIVE")

    def test_roundtrip(self):
        d = DyadicInterval.from_decimal_bounds("-0.125", "0.75", bits=64)
        self.assertEqual(DyadicInterval.from_json(d.to_json()), d)

    def test_reject_reversed(self):
        with self.assertRaises(IntervalCodecError):
            DyadicInterval.from_decimal_bounds("2", "1")


if __name__ == "__main__":
    unittest.main()
