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

    def test_merged_pr_285_is_the_theorem_anchor(self):
        anchor = self.state["merged_theorem_anchor"]
        self.assertEqual(anchor["pr"], 285)
        self.assertEqual(anchor["validated_head"], HEAD)
        self.assertEqual(anchor["merge_commit"], MERGE)
        self.assertEqual(anchor["tree"], TREE)
        self.assertEqual(anchor["status"], "MERGED_GREEN_THEOREM_STATE")
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(delta["pr"], 285)
        self.assertEqual(delta["prior_theorem_authority_pr"], 284)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_candidate_is_pr_287_pending_and_previous_candidate_is_history(self):
        # PR #287 (post-285 M70-M77 build) is an open candidate; nothing in it is
        # merged authority until its exact-head CI receipt exists.
        candidate = self.state["candidate_branch"]
        self.assertEqual(candidate["pr"], 287)
        self.assertEqual(candidate["theorem_validation"], "CI_PENDING_EXACT_HEAD_RUNTIME_RECEIPT_REQUIRED")
        self.assertFalse(candidate["terminal_claim_change"])
        previous = self.state["previous_candidate_branch"]
        self.assertEqual(previous["pr"], 283)
        self.assertIn("PR #284", previous["outcome"])

    def test_post285_frontier_keeps_f04_m74_unmerged_and_rh_open(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post285_source_inertia_package"], "PROVED_MERGED_PR_285")
        # Candidate #287 proves these pending CI; none is merged authority.
        pending = "PROVED_PENDING_CI_CANDIDATE_PR_287"
        self.assertEqual(route["post285_f04_production_derivative_authority"], pending)
        self.assertEqual(route["post285_m74_canonical_secular_instantiation"], pending)
        self.assertIn(pending, route["post285_general_omega_inertia"])
        self.assertIn("FILTERED_CARRIERS_OPEN", route["post285_general_omega_inertia"])
        for key in (
            "post285_f04_production_derivative_authority",
            "post285_m74_canonical_secular_instantiation",
            "post285_general_omega_inertia",
        ):
            self.assertNotIn("MERGED", route[key])
        self.assertEqual(
            route["current_active_subobligation"],
            "OBS-060O_CONTACT_CONDITIONED_PRODUCTION_SATURATION_EXCLUSION",
        )
        for token in ("PR #285", "RH remains OPEN", "Candidate PR #287", "pending exact-head CI"):
            self.assertIn(token, self.state["current_control_note"])

    def test_post285_registered_claims_are_individually_bound(self):
        by_id = {c["id"]: c for c in self.registry["claims"]}
        rows = self.matrix["post285_registered_claims"]
        self.assertEqual(
            [row["id"] for row in rows],
            self.state["active_research_route"]["post285_registered_claims"],
        )
        self.assertEqual(
            self.state["latest_validated_theorem_delta"]["supporting_declarations"],
            [row["theorem"] for row in rows],
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

    def test_f04_conditional_claims_stay_open(self):
        by_id = {c["id"]: c for c in self.registry["claims"]}
        for cid in (
            "R003_WEIGHTED_PRODUCTION_PAIR_BALANCE",
            "R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER",
            "C_RH",
        ):
            self.assertEqual(by_id[cid]["status"], "OPEN")


if __name__ == "__main__":
    unittest.main()
