import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post278SyncTests(unittest.TestCase):
    def test_post278_history_survives_post279_authority(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        theorem = state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 279)
        self.assertEqual(
            theorem["validated_head"],
            "a716d62f386ac6d43c70672c68ac316b62a613e2",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "5b2d78f637b4646fe0b2f4395880b92173d7425e",
        )
        self.assertEqual(
            theorem["tree"],
            "7458574c81c65fbec71239e21a1221e2469108d4",
        )
        candidate = state["candidate_branch"]
        self.assertEqual(candidate["pr"], 280)
        self.assertEqual(
            candidate["branch"],
            "research/post279-lifted-contact-quotient",
        )
        self.assertEqual(
            candidate["status"],
            "POST279_LIFTED_CONTACT_SOURCE_QUOTIENT_CANDIDATE",
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
            "SOURCE_DERIVED_CONTACT_QUOTIENT_EQUALITY_RIGIDITY",
        )
        self.assertIn("PRODUCTION_SOURCE", route["current_next_research_target"])

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
