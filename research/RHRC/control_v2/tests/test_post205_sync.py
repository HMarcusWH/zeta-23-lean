import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post205SyncTests(unittest.TestCase):
    def test_authority_split_preserves_research_anchor_while_theorem_state_advances(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertGreaterEqual(state["merged_theorem_anchor"]["pr"], 184)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")
        note = state["control_note"]
        for token in (
            "PR #184",
            "6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e",
        ):
            self.assertIn(token, note)

        # #205 is historical research authority, not a forever-current pointer.
        # Preserve its exact provenance in the append-only control history while
        # allowing later research PRs to advance latest_research_evidence.
        self.assertGreaterEqual(state["latest_research_evidence"]["pr"], 205)
        for token in (
            "PR #205",
            "73b78297da54b9f5b2d47584a8033356a6b2e2a8",
            "deaa69ae190ada511cf8228f174846184673ff3a",
            "3d715612eabf25a9056ab84b0c5e968f71354666",
            "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
            "fixture C1",
            "N=2",
            "K=3",
            "even predecessor form=70",
            "odd predecessor form=10",
            "even witness energy=-130",
            "odd witness energy=-410",
            "selected even root=-13/42",
            "canonical_realizability=false",
        ):
            self.assertIn(token, note)

    def test_living_docs_advance_through_205_without_erasing_history(self):
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
        for path in paths:
            text = path.read_text(encoding="utf-8")
            with self.subTest(path=path):
                for token in (
                    "#184",
                    "#190",
                    "#192",
                    "#193",
                    "#195",
                    "#197",
                    "#199",
                    "#201",
                    "#203",
                    "#205",
                ):
                    self.assertIn(token, text)
                self.assertIn("PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED", text)
                self.assertIn("GLOBAL_MONOTONE_ORIENTATION", text)
                self.assertIn("J_POSITIVE", text)
                self.assertIn("RH remains OPEN", text)

    def test_current_plan_routes_pair_d_to_canonical_arithmetic(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "latest merged research PR = #205",
            "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
            "even predecessor form = 70 > 0",
            "odd predecessor form  = 10 > 0",
            "even successor witness energy = -130",
            "odd successor witness energy  = -410",
            "selected even compressed root = -13/42",
            "canonical_realizability = false",
            "OBS-059 OPEN / ACTIVE / CANONICAL-ARITHMETIC ONLY",
            "generic structural Pair-D simultaneous-bad exclusion = EXACTLY FALSIFIED BY #205 C1",
            "Pair D canonical-arithmetic squeeze = HIGHEST INFORMATION / ACTIVE",
            "Pair B negative-index vs localized critical-line sampling rigidity = SECONDARY",
            "genericQuadraticNormalPairing",
            "sourceMoment <-> M4",
            "odd-selected first-bad closure",
        ):
            self.assertIn(token, text)

    def test_route_registry_preserves_machine_semantics_and_advances_note(self):
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
            "PR #205",
            "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
            "even predecessor form 70",
            "odd predecessor form 10",
            "even successor witness energy -130",
            "odd successor witness energy -410",
            "selected even compressed root -13/42",
            "canonical_realizability=false",
            "genericQuadraticNormalPairing",
            "Pair B",
            "OBS-059",
            "No claim_ids are changed by this synchronization",
        ):
            self.assertIn(token, note)

    def test_action_registry_semantics_are_unchanged(self):
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

    def test_countermodel_registry_promotes_only_c1(self):
        text = (RHRC / "countermodels" / "README.md").read_text(encoding="utf-8")
        for token in (
            "Post-#205 executable C1 promotion",
            "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
            "check_post204_pair_d_exact_geometry.py",
            "check_post204_pair_d_scope.py",
            "certify_post204_pair_d_structural_countermodel.py",
            "EXACT EXECUTABLE RESEARCH",
            "RIGOROUS FINITE SYNTHETIC COUNTERMODEL",
            "does not recover the missing original 37-case oracle",
            "canonicalSourceMatrix",
        ):
            self.assertIn(token, text)

    def test_post205_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_205_PAIR_D_STRUCTURAL_COUNTERMODEL_DELTA.md"
        ).read_text(encoding="utf-8")
        for heading in (
            "# What became formally true",
            "# What became research-certified",
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
            "PAIR_D_GENERIC_SIMULTANEOUS_BAD_COUNTERMODEL_CERTIFIED",
            "canonical_realizability = false",
            "genericQuadraticNormalPairing",
            "canonical sourceMoment <-> M4 rigidity",
            "Pair B",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_obstruction_delta_narrows_obs059_without_closing_it(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_205_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-056",
            "OBS-057",
            "OBS-058",
            "OBS-059",
            "OPEN / ACTIVE / CANONICAL-ARITHMETIC ONLY",
            "EXACTLY FALSIFIED BY #205 C1",
            "canonical simultaneous even/odd bad exclusion",
            "canonical sourceMoment <-> M4 rigidity",
            "same-state canonical arithmetic composition",
            "odd-selected first-bad closure",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_dead_route_delta_strengthens_existing_routes_only(self):
        text = (RHRC / "DEAD_ROUTES_POST_205_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "DR-012",
            "DR-013",
            "does not introduce a new dead-route family",
            "even predecessor form = 70",
            "odd predecessor form = 10",
            "even witness energy = -130",
            "odd witness energy = -410",
            "selected even compressed root = -13/42",
            "canonical sourceMoment <-> M4 rigidity",
            "DR-028",
            "RH remain OPEN",
        ):
            self.assertIn(token.lower(), text.lower())

    def test_claim_surfaces_remain_unpromoted(self):
        registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        bindings = json.loads((RHRC / "R003_PROMOTED_BINDINGS.json").read_text(encoding="utf-8"))
        state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))
        route_registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        route = next(r for r in route_registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(state["terminal_claim"], "RH_OPEN")
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])
        self.assertIsNone(route["route_spec_digest"])
        self.assertIsNone(route["boundary_digest"])
        self.assertIsInstance(registry, dict)
        self.assertIsInstance(bindings, dict)


if __name__ == "__main__":
    unittest.main()
