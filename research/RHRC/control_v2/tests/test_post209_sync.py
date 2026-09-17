import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post209SyncTests(unittest.TestCase):
    def test_three_anchor_model(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        theorem = state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 209)
        self.assertEqual(
            theorem["validated_head"],
            "a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "e029af769e01a547ebbc6ed045509bb2cbdd6cff",
        )
        self.assertEqual(
            theorem["tree"],
            "6a75278ebf3f2bd19a77419238872cb81835ec13",
        )
        self.assertEqual(theorem["status"], "MERGED_GREEN_THEOREM_STATE")

        research = state["latest_research_evidence"]
        self.assertEqual(research["pr"], 205)
        self.assertEqual(
            research["disposition"],
            "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
        )
        self.assertFalse(research["canonical_realizability"])

        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["active_research_route"]["formal_first_break"], "E4A4-SCHUR-FB-05")
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

    def test_active_route_records_209_without_changing_control_semantics(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        route = state["active_research_route"]
        self.assertEqual(route["even_selected_odd_good_branch"], "PROVED_THROUGH_PR_209")
        self.assertEqual(route["pair_d_quantitative_coercivity"], "PROVED_PR_209")
        self.assertEqual(route["mixed_jet_antialignment"], "PROVED_PR_209")
        self.assertEqual(route["riesz_eight_nine_nondegeneracy"], "PROVED_PR_209")
        self.assertEqual(route["canonical_simultaneous_odd_bad_branch"], "OPEN")
        self.assertEqual(route["odd_selected_first_bad_branch"], "OPEN")
        self.assertEqual(route["closed_subobligation"], "OBS-059Q")
        self.assertEqual(route["active_subobligation"], "OBS-059I")
        self.assertEqual(
            route["required_new_information"],
            "INDEPENDENT_COMPLETE_CANONICAL_FUNCTIONAL_INCOMPATIBILITY",
        )

    def test_post209_research_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_209_PAIR_D_COERCIVITY_ANTI_ALIGNMENT_DELTA.md"
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
            "a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392",
            "e029af769e01a547ebbc6ed045509bb2cbdd6cff",
            "6a75278ebf3f2bd19a77419238872cb81835ec13",
            "oddBad_or_sourceMomentMixedJet_re_neg_of_even",
            "evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad",
            "quantitative compensation law",
            "INDEPENDENT",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_post209_obstruction_delta_closes_q_and_opens_i(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_209_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-059Q",
            "CLOSED / PROVED BY #209",
            "OBS-059I",
            "OPEN / ACTIVE",
            "PROVED THROUGH #209",
            "canonical simultaneous odd-bad branch",
            "odd-selected first-bad closure",
            "endpointScalar",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_current_plan_advances_to_209_frontier(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "Post-#209 authoritative execution state",
            "THEOREM AUTHORITY = PR #209",
            "LATEST RESEARCH EVIDENCE = PR #205",
            "even-selected + odd-good retained branch = PROVED THROUGH #209",
            "OBS-059Q = CLOSED / PROVED BY #209",
            "OBS-059I = OPEN / ACTIVE",
            "independent complete canonical functional",
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