import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post207SyncTests(unittest.TestCase):
    def test_three_anchor_model(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        theorem = state["merged_theorem_anchor"]
        self.assertEqual(theorem["pr"], 207)
        self.assertEqual(
            theorem["validated_head"],
            "7e186ede13beece95e8a08b2449cd3accbe5b2f5",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "76cf4e3b5ef4b7ab904a861b6d4cb01fdcd8d0e0",
        )
        self.assertEqual(
            theorem["tree"],
            "d6509407cc7b667b0ff3e7faab2acd525ae32db9",
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

    def test_living_docs_synchronize_post207_theorem_frontier(self):
        paths = (
            ROOT / "README.md",
            ROOT / "AUDIT.md",
            ROOT / "FORK_NOTES.md",
            RHRC / "README.md",
            RHRC / "CURRENT_RESEARCH_PLAN.md",
            RHRC / "DOCUMENTATION_AUTHORITY.md",
            RHRC / "RESEARCH_LEADS.md",
            RHRC / "VALIDATION_PROTOCOL.md",
            RHRC / "FB05_INCOMPATIBILITY_PROGRAM.md",
            RHRC / "routes" / "R003_ccm_bridge" / "README.md",
            RHRC / "control_v2" / "README.md",
        )
        theorem_tokens = (
            "#207",
            "7e186ede13beece95e8a08b2449cd3accbe5b2f5",
            "76cf4e3b5ef4b7ab904a861b6d4cb01fdcd8d0e0",
            "d6509407cc7b667b0ff3e7faab2acd525ae32db9",
            "evenShiftedSourceMomentMomentFour_re_pos_of_even_of_not_oddBad",
            "evenShiftedMomentFour_ne_zero_of_even_of_not_oddBad",
            "evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad",
            "oddBad_or_sourceMomentMomentFour_re_pos_of_even",
            "SUPERSEDED / UNNECESSARY",
            "RH remains OPEN",
        )
        for path in paths:
            text = path.read_text(encoding="utf-8")
            with self.subTest(path=path):
                for token in theorem_tokens:
                    self.assertIn(token, text)
                self.assertIn("#205", text)
                self.assertIn("PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED", text)

    def test_current_plan_splits_obs059_correctly(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "THEOREM AUTHORITY = PR #207",
            "LATEST RESEARCH EVIDENCE = PR #205",
            "even-selected + odd-good retained branch = PROVED THROUGH #207",
            "canonical simultaneous odd-bad branch = OPEN",
            "odd-selected first-bad branch = OPEN",
            "unconditional sourceMoment -> M4 implication = NOT PROVED",
            "quantitative coercivity",
            "-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)",
        ):
            self.assertIn(token, text)

    def test_route_registry_preserves_machine_semantics_and_records_207(self):
        registry = json.loads(
            (RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8")
        )
        route = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])
        self.assertIsNone(route["route_spec_digest"])
        self.assertIsNone(route["boundary_digest"])
        note = route["note"]
        for token in (
            "PR #207",
            "oddBad_or_sourceMomentMomentFour_re_pos_of_even",
            "even-selected odd-good branch",
            "simultaneous odd-bad branch remains open",
            "genericQuadraticNormalPairing",
            "SUPERSEDED / UNNECESSARY",
            "No claim_ids are changed by this synchronization",
        ):
            self.assertIn(token, note)

    def test_action_registry_semantics_remain_unchanged(self):
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            registry["current_frontier"],
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN",
        )
        action = registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]
        self.assertEqual(action["concept_id"], "canonical_source_exclusion")
        self.assertEqual(
            action["score_inputs"],
            {
                "cost": 2.0,
                "information_gain": 5.0,
                "falsification_value": 5.0,
                "closure_value": 5.0,
                "residual_risk": 1.8,
                "dependency_debt": 0.8,
            },
        )
        self.assertEqual([b["id"] for b in action["first_breaks"]], ["E4A4-SCHUR-FB-05"])

    def test_post207_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_207_PAIR_D_SOURCE_M4_ENERGY_DELTA.md"
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
            "oddBad_or_sourceMomentMomentFour_re_pos_of_even",
            "0 < re (star(explicitCanonicalSourceMoment(v)) * M4(v))",
            "unconditional theorem",
            "-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)",
            "DERIVED / not yet separately formalized",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_obstruction_delta_keeps_open_branches_open(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_207_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-059",
            "FALSIFIED / CONSUMED BY #205",
            "PROVED THROUGH #207",
            "canonical simultaneous odd-bad branch",
            "odd-selected first-bad closure",
            "same-state terminal incompatibility",
            "SUPERSEDED / UNNECESSARY",
            "OBS-059Q",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_claim_surfaces_remain_unpromoted(self):
        claim_registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        bindings = json.loads((RHRC / "R003_PROMOTED_BINDINGS.json").read_text(encoding="utf-8"))
        registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        route = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])
        self.assertIsInstance(claim_registry, dict)
        self.assertIsInstance(bindings, dict)


if __name__ == "__main__":
    unittest.main()
