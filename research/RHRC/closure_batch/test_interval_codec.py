from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
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

    def test_exact_rational_string_bounds(self):
        d = DyadicInterval.from_decimal_bounds("-1/2", "1/2", bits=16)
        self.assertEqual(d.lo, Fraction(-1, 2))
        self.assertEqual(d.hi, Fraction(1, 2))

    def test_exact_dyadic_fraction_bounds(self):
        d = DyadicInterval.from_fraction_bounds(Fraction(-3, 8), Fraction(5, 16))
        self.assertEqual(d.lo, Fraction(-3, 8))
        self.assertEqual(d.hi, Fraction(5, 16))

    def test_reject_non_dyadic_exact_fraction(self):
        with self.assertRaises(IntervalCodecError):
            DyadicInterval.from_fraction_bounds(Fraction(1, 3), Fraction(1, 2))

    def test_reject_reversed(self):
        with self.assertRaises(IntervalCodecError):
            DyadicInterval.from_decimal_bounds("2", "1")

    def test_reject_bool_integer_fields(self):
        for key in ("lo_num", "hi_num", "exp2"):
            obj={"lo_num":0,"hi_num":1,"exp2":4}
            obj[key]=True
            with self.subTest(key=key), self.assertRaises(IntervalCodecError):
                DyadicInterval.from_json(obj)

    def test_reject_fractional_json_integer(self):
        with self.assertRaises(IntervalCodecError):
            DyadicInterval.from_json({"lo_num":0.5,"hi_num":1,"exp2":4})

    def test_reject_nonfinite_decimal(self):
        with self.assertRaises(IntervalCodecError):
            DyadicInterval.from_decimal_bounds("nan","1")

    def test_contains_interval(self):
        outer=DyadicInterval(-4,8,4)
        inner=DyadicInterval(-1,2,4)
        self.assertTrue(outer.contains_interval(inner))

    def test_arb_roundtrip_when_flint_available(self):
        try:
            from flint import arb, ctx
        except Exception:
            self.skipTest("python-flint unavailable in lightweight framework")
        old=ctx.prec
        try:
            ctx.prec=192
            for text in ["0", "1.25", "-3.5", "1e-40", "-1e30"]:
                x=arb(text)
                # add a nonzero radius in Arb syntax
                b=x + arb("1e-50")
                d=DyadicInterval.from_arb(b)
                lo=b.lower().man_exp()
                hi=b.upper().man_exp()
                self.assertLessEqual(d.lo, Fraction(int(lo[0]),1) * Fraction(2) ** int(lo[1]))
                self.assertGreaterEqual(d.hi, Fraction(int(hi[0]),1) * Fraction(2) ** int(hi[1]))
        finally:
            ctx.prec=old


if __name__ == "__main__":
    unittest.main()
