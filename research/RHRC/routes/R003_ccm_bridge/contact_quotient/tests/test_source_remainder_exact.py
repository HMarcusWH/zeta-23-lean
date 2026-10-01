from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_source_remainder_exact import run_checks


class ExactSourceRemainderTests(unittest.TestCase):
    def test_exact_source_remainder_receipt(self):
        receipt = run_checks()
        self.assertEqual(receipt["status"], "PASS")
        self.assertEqual(receipt["passed"], receipt["total"])
        self.assertFalse(receipt["equality_rigidity_proved"])
        self.assertFalse(receipt["unconditional_RH_proved"])
        self.assertEqual(receipt["terminal_claim"], "RH_OPEN")


if __name__ == "__main__":
    unittest.main()
