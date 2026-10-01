from __future__ import annotations

import unittest

from feature_registry import active_feature_ids, load_registry


class FeatureRegistryTests(unittest.TestCase):
    def test_registry_is_claim_capped_and_unique(self):
        data = load_registry()
        self.assertEqual(data["terminal_claim"], "RH_OPEN")
        self.assertFalse(data["theorem_promotion"])
        ids = active_feature_ids(data)
        self.assertEqual(len(ids), len(set(ids)))

    def test_paper_saturation_is_not_default_rank_authority(self):
        data = load_registry()
        self.assertTrue(data["paper_relations"])
        self.assertTrue(
            all(
                row["authority"] == "PAPER_DERIVED_NOT_LEAN"
                for row in data["paper_relations"]
            )
        )


if __name__ == "__main__":
    unittest.main()
