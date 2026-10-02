import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post278SyncTests(unittest.TestCase):
    def test_post278_history_survives_post280_authority(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        theorem = state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 280)
        self.assertEqual(
            theorem["validated_head"],
            "3e897765c788c0cbb2b57fa75da62ef0e1766dca",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "752e59f7147eec183e649ebe1e9af4d0329dbe73",
        )
        self.assertEqual(
            theorem["tree"],
            "807c2cdec6c6fa09cb0ba65915112c9c2dfd19ba",
        )
        candidate = state["candidate_branch"]
        self.assertEqual(candidate["pr"], 281)
        self.assertEqual(
            candidate["branch"],
            "research/post280-production-saturation-frontier",
        )
        self.assertEqual(
            candidate["status"],
            "POST280_PRODUCTION_SATURATION_FRONTIER_CANDIDATE",
        )
        self.assertEqual(candidate["theorem_validation"], "CI_PENDING")
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

    def test_post278_claim_inventory(self):
        registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        by_id = {c["id"]: c for c in registry["claims"]}
        required = {
            "R003_SMALL_APERTURE_GROUND_SPECTRUM",
            "R003_EVENTUAL_APERTURE_PARITY_BADNESS_FROM_OFFLINE_ZERO",
            "R003_FIXED_N_GROUND_SIGN_OPPOSITION",
            "R003_FIXED_N_GROUND_CONTINUITY",
            "R003_OFFLINE_ZERO_FIXED_N_ZERO_CONTACT",
            "R003_OFFLINE_ZERO_ONE_STEP_DOMINATION_FAILURE",
            "AUDIT_GLOBAL_GROUND_PROPAGATION_IMPLIES_RH",
            "AUDIT_UNIFORM_DOMINATION_IMPLIES_RH",
        }
        self.assertTrue(required.issubset(by_id))
        for cid in required:
            self.assertEqual(by_id[cid]["status"], "PROVED_UNCONDITIONAL")
        open_ids = {c["id"] for c in registry["claims"] if c["status"] == "OPEN"}
        self.assertEqual(
            open_ids,
            {
                "C_RH",
                "R001_PRIME_UPPER",
                "R002_WINDOWED_VISIBILITY",
                "R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES",
            },
        )

    def test_first_crossing_frontier_advanced_without_erasing_post278(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        route = state["active_research_route"]
        self.assertEqual(
            route["post278_fixedN_ground_continuity"],
            "PROVED_MERGED_PR_278",
        )
        self.assertEqual(
            route["post278_sameN_zero_contact"],
            "PROVED_MERGED_PR_278",
        )
        self.assertEqual(
            route["post279_first_crossing_shell"],
            "PROVED_MERGED_PR_279",
        )
        self.assertEqual(
            route["current_active_subobligation"],
            "PRODUCTION_OPTIMIZED_CURVATURE_BRIDGE_AND_SATURATION_GAP_MEASUREMENT",
        )
        self.assertEqual(route["current_next_research_target"], "PRODUCTION_ARITHMETIC_SATURATION_FRONTIER")

    def test_frozen_pr274_campaign_provenance_is_not_rewritten(self):
        campaign = json.loads(
            (RHRC / "closure_batch" / "CAMPAIGN_STATE.json").read_text(encoding="utf-8")
        )
        plan = json.loads((RHRC / "closure_batch" / "PLAN.json").read_text(encoding="utf-8"))
        self.assertEqual(campaign["pr"], 274)
        self.assertEqual(plan["pr"], 274)

    def test_track_b_strength_reclassification(self):
        obligations = json.loads(
            (RHRC / "closure_batch" / "OBLIGATIONS.json").read_text(encoding="utf-8")
        )
        by_id = {r["id"]: r for r in obligations["obligations"]}
        self.assertEqual(by_id["B2_UNIFORM_DOMINATION"]["status"], "OPEN")
        self.assertEqual(by_id["B3_DOMINATION_TO_ALL_APERTURE"]["status"], "PROVED")
        self.assertEqual(
            by_id["B3_DOMINATION_TO_ALL_APERTURE"]["lean_target"],
            "Zeta23.RHRC.canonicalAllAperturePositivity_of_canonicalUniformDomination",
        )
        self.assertIn(["B2_UNIFORM_DOMINATION"], by_id["RH_FINAL"]["alternative_premise_sets"])
        self.assertNotIn(["B3_DOMINATION_TO_ALL_APERTURE"], by_id["RH_FINAL"]["alternative_premise_sets"])


if __name__ == "__main__":
    unittest.main()
