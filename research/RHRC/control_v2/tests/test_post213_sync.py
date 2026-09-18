import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post213SyncTests(unittest.TestCase):
    def test_three_anchor_model(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        theorem = state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 213)
        self.assertEqual(theorem["validated_head"], "703c3764a7d35aa4801e791a1929efa54c2533a1")
        self.assertEqual(theorem["merge_commit"], "ee341a6071d177c75bbea0a5f92ebe3b3bb16696")
        self.assertEqual(theorem["tree"], "db00686b2bbb821adb857e5c68f422d19c4f91cd")
        self.assertEqual(theorem["status"], "MERGED_GREEN_THEOREM_STATE")
        self.assertEqual(state["latest_research_evidence"]["pr"], 205)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

    def test_active_route_records_kernel_closure_without_closing_obstruction(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        route = state["active_research_route"]
        self.assertEqual(route["even_selected_odd_good_branch"], "PROVED_THROUGH_PR_213")
        self.assertEqual(route["pair_d_quantitative_coercivity"], "PROVED_PR_209")
        self.assertEqual(route["complete_source_functional_representation"], "PROVED_PR_211")
        self.assertEqual(route["complete_physical_rhs"], "PROVED_PR_213")
        self.assertEqual(route["source_coordinate_kernel_representation"], "PROVED_PR_213")
        self.assertEqual(route["retained_source_kernel_antialignment_rewrite"], "PROVED_PR_213")
        self.assertEqual(route["source_coordinate_kernel_subobligation"], "CLOSED_PROVED_PR_213")
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(
            route["required_new_information"],
            "INDEPENDENT_COMPLETE_CANONICAL_FUNCTIONAL_INCOMPATIBILITY",
        )
        self.assertEqual(route["next_research_target"], "EXACT_KERNEL_ADVERSARIAL_FALSIFICATION")
        self.assertEqual(route["canonical_simultaneous_odd_bad_branch"], "OPEN")
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")

    def test_post213_research_delta_has_required_post_green_sections(self):
        text = (RHRC / "RESEARCH_LEADS_POST_213_COMPLETE_SOURCE_KERNEL_DELTA.md").read_text(encoding="utf-8")
        for heading in (
            "# What became formally true",
            "# What changed",
            "# Upstream implications",
            "# Downstream implications",
            "# Resurrected routes",
            "# New RH-relevant clues",
            "# Falsification checks",
            "# Highest-leverage next moves",
            "# Standing questions",
        ):
            self.assertIn(heading, text)
        for token in (
            "703c3764a7d35aa4801e791a1929efa54c2533a1",
            "ee341a6071d177c75bbea0a5f92ebe3b3bb16696",
            "db00686b2bbb821adb857e5c68f422d19c4f91cd",
            "half_literatureRHS_dictionaryMixedTest_eq_completePhysicalRHS_of_zero",
            "canonicalQuadraticNormalSourceFunctional_eq_sourceKernelRHS",
            "explicitCanonicalSourceMoment_eq_sourceKernelRHS",
            "oddBad_or_sourceKernelMixedJet_re_neg_of_even",
            "EXACT_KERNEL_ADVERSARIAL_FALSIFICATION",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_post213_obstruction_delta_keeps_obs059i_open(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_213_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-059I",
            "OPEN / ACTIVE / REPRESENTATION AND KERNEL LAYERS CLOSED",
            "CLOSED / PROVED BY #211",
            "CLOSED / PROVED BY #213",
            "EXACT_KERNEL_ADVERSARIAL_FALSIFICATION",
            "canonical simultaneous odd-bad branch",
            "odd-selected first-bad closure",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_current_plan_advances_to_kernel_falsification(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "Post-#213 authoritative execution state",
            "THEOREM AUTHORITY = PR #213",
            "STEP 5",
            "CLOSED / PROVED #213",
            "STEP 6",
            "OPEN / ACTIVE / OBS-059I",
            "EXACT_KERNEL_ADVERSARIAL_FALSIFICATION",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_claim_and_route_surfaces_remain_unpromoted(self):
        action_registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        claim_registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        bindings = json.loads((RHRC / "R003_PROMOTED_BINDINGS.json").read_text(encoding="utf-8"))
        registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        route = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(action_registry["current_frontier"], "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN")
        action = action_registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]
        self.assertEqual([b["id"] for b in action["first_breaks"]], ["E4A4-SCHUR-FB-05"])
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])
        self.assertIsNone(route["route_spec_digest"])
        self.assertIsNone(route["boundary_digest"])
        self.assertIsInstance(claim_registry, dict)
        self.assertIsInstance(bindings, dict)


if __name__ == "__main__":
    unittest.main()
