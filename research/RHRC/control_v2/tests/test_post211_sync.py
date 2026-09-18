import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post211SyncTests(unittest.TestCase):
    """Preserve the #211 synchronization contract after later theorem anchors advance."""
    def test_current_state_has_advanced_but_preserves_211_history(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertGreaterEqual(state["merged_theorem_anchor"]["pr"], 211)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")
        note = state["control_note"]
        for token in (
            "PR #211",
            "704a69e41871269814ba091e9476fe76b2d09844",
            "dd42e6368e48957c9922a9e917e10f60a2582b9f",
            "a735f6149aeaa9f8358394c33fd6dcee8062f68e",
            "explicitCanonicalSourceMoment_eq_completeSourceFunctional",
            "oddBad_or_completeSourceFunctionalMixedJet_re_neg_of_even",
        ):
            self.assertIn(token, note)

    def test_active_route_records_211_without_erasing_209_provenance(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        route = state["active_research_route"]
        self.assertIn(route["even_selected_odd_good_branch"], ("PROVED_THROUGH_PR_211", "PROVED_THROUGH_PR_213"))
        self.assertEqual(route["pair_d_quantitative_coercivity"], "PROVED_PR_209")
        self.assertEqual(route["mixed_jet_antialignment"], "PROVED_PR_209")
        self.assertEqual(route["riesz_eight_nine_nondegeneracy"], "PROVED_PR_209")
        self.assertEqual(route["mixed_dictionary_pairing"], "PROVED_PR_211")
        self.assertEqual(route["complete_source_functional_representation"], "PROVED_PR_211")
        self.assertEqual(route["same_observable_global_local_interface"], "PROVED_PR_211")
        self.assertEqual(route["complete_functional_antialignment_rewrite"], "PROVED_PR_211")
        self.assertEqual(route["representation_prerequisite"], "CLOSED_PROVED_PR_211")
        self.assertEqual(
            route["next_theoremization"],
            "SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL",
        )
        self.assertEqual(route["closed_subobligation"], "OBS-059Q")
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(
            route["required_new_information"],
            "INDEPENDENT_COMPLETE_CANONICAL_FUNCTIONAL_INCOMPATIBILITY",
        )
        self.assertEqual(route["canonical_simultaneous_odd_bad_branch"], "OPEN")
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")

    def test_post211_research_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_211_COMPLETE_FUNCTIONAL_REPRESENTATION_DELTA.md"
        ).read_text(encoding="utf-8")
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
            "704a69e41871269814ba091e9476fe76b2d09844",
            "dd42e6368e48957c9922a9e917e10f60a2582b9f",
            "a735f6149aeaa9f8358394c33fd6dcee8062f68e",
            "literatureRHS_dictionaryMixedTest_eq_matrixCoefficientPairing",
            "explicitCanonicalSourceMoment_eq_completeSourceFunctional",
            "oddBad_or_completeSourceFunctionalMixedJet_re_neg_of_even",
            "SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_post211_obstruction_delta_keeps_i_open(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_211_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-059I",
            "OPEN / ACTIVE / REPRESENTATION LAYER CLOSED",
            "CLOSED / PROVED BY #211",
            "SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL",
            "INDEPENDENT_COMPLETE_CANONICAL_FUNCTIONAL_INCOMPATIBILITY",
            "canonical simultaneous odd-bad branch",
            "odd-selected first-bad closure",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_current_plan_advances_to_211_frontier(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "Post-#211 authoritative execution state",
            "THEOREM AUTHORITY = PR #211",
            "LATEST RESEARCH EVIDENCE = PR #205",
            "Identify complete source moment with Λ_L(h)",
            "SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL",
            "OBS-059I = OPEN / ACTIVE",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_action_registry_and_claim_surfaces_remain_unpromoted(self):
        action_registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        claim_registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        bindings = json.loads((RHRC / "R003_PROMOTED_BINDINGS.json").read_text(encoding="utf-8"))
        route_registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        route = next(r for r in route_registry["routes"] if r["route_id"] == "R003_ccm_bridge")

        self.assertEqual(
            action_registry["current_frontier"],
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN",
        )
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
