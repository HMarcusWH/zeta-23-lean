from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from countermodel_controls import replay_controls


class CountermodelControlTests(unittest.TestCase):
    def test_generic_and_pair_d_negative_controls(self):
        receipt = replay_controls()
        self.assertEqual(receipt["status"], "PASS")
        self.assertEqual(receipt["claim_cap"], "NEGATIVE_CONTROLS_ONLY")
        self.assertTrue(receipt["pair_d_c1"]["simultaneous_badness"])
        self.assertFalse(receipt["pair_d_c1"]["canonical_realizability"])
        self.assertEqual(receipt["terminal_claim"], "RH_OPEN")


if __name__ == "__main__":
    unittest.main()
