import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
STATE = RHRC / "control_v2" / "CONTROL_STATE.json"
POST284 = RHRC / "integration" / "post284"

HEAD = "d20653c50e85ed927940ffe7723cf07a1008be7d"
MERGE = "18a63cc5a3bb857cd603b073790427184e75d7f6"
TREE = "f95a9d07d987199d85763990b7760deb7619d601"


class Post285SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(STATE.read_text(encoding="utf-8"))
        self.registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        self.matrix = json.loads((POST284 / "CLAIM_MIGRATION_MATRIX.json").read_text(encoding="utf-8"))

    def test_merged_pr_285_authority_is_superseded_not_erased(self):
        # PR #287 is now the merged theorem anchor; PR #285 stays merged
        # authority for its own package and the prior-authority link.
        anchor = self.state["merged_theorem_anchor"]
        self.assertGreater(anchor["pr"], 285)
        self.assertNotEqual(anchor["merge_commit"], MERGE)
        self.assertEqual(anchor["status"], "MERGED_GREEN_THEOREM_STATE")
        self.assertEqual(self.state["latest_validated_theorem_delta"]["prior_theorem_authority_pr"], 285)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_previous_candidate_is_history(self):
        previous = self.state["previous_candidate_branch"]
        self.assertEqual(previous["pr"], 283)
        self.assertIn("PR #284", previous["outcome"])

    def test_post285_package_stays_merged_and_rh_open(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post285_source_inertia_package"], "PROVED_MERGED_PR_285")
        self.assertEqual(
            route["current_active_subobligation"],
            "OBS-060O_CONTACT_CONDITIONED_PRODUCTION_SATURATION_EXCLUSION",
        )
        for token in ("PR #285", "RH remains OPEN"):
            self.assertIn(token, self.state["current_control_note"])

    def test_post285_registered_claims_are_individually_bound(self):
        by_id = {c["id"]: c for c in self.registry["claims"]}
        rows = self.matrix["post285_registered_claims"]
        self.assertEqual(
            [row["id"] for row in rows],
            self.state["active_research_route"]["post285_registered_claims"],
        )
        for row in rows:
            claim = by_id[row["id"]]
            self.assertEqual(claim["status"], "PROVED_UNCONDITIONAL")
            self.assertEqual(claim["theorem"], row["theorem"])
            self.assertEqual(claim["source"], row["source"])
            self.assertEqual(claim["route"], "R003_ccm_bridge")
            self.assertFalse(row["F04_premise"])
            self.assertIn(HEAD, claim["note"])
            self.assertIn("No contact exclusion and no RH.", claim["note"])

    def test_rh_stays_open(self):
        by_id = {c["id"]: c for c in self.registry["claims"]}
        self.assertEqual(by_id["C_RH"]["status"], "OPEN")


if __name__ == "__main__":
    unittest.main()
