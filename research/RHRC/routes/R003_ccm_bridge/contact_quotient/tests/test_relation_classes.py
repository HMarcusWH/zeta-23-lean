from __future__ import annotations

import unittest

from canonical_vs_synthetic import compare
from staged_rank_audit import staged_audit


class RelationClassTests(unittest.TestCase):
    def test_canonical_source_adds_relation_rank(self):
        result = compare()
        self.assertEqual(result["terminal_claim"], "RH_OPEN")
        self.assertGreater(
            result["stages"][-1]["canonical_rank"],
            result["stages"][-1]["synthetic_rank"],
        )

    def test_exact_rank_is_not_terminal_claim(self):
        result = staged_audit(canonical=True)
        self.assertEqual(result["terminal_claim"], "RH_OPEN")
        self.assertFalse(result["theorem_promotion"])
        self.assertIn("NOT_POINTWISE_CONTACT_EXCLUSION", result["rank_semantics"])


if __name__ == "__main__":
    unittest.main()
