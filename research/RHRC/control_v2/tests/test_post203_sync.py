import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post203SyncTests(unittest.TestCase):
    def test_authority_split_advances_research_only(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertEqual(state["merged_theorem_anchor"]["pr"], 184)
        self.assertEqual(
            state["merged_theorem_anchor"]["merge_commit"],
            "6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e",
        )
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

        research = state["latest_research_evidence"]
        self.assertEqual(research["pr"], 203)
        self.assertEqual(
            research["validated_head"],
            "c8196830a8b49e657b28d36b364e1cff68c568d6",
        )
        self.assertEqual(
            research["merge_commit"],
            "ab660e812a78d482145eadc3e42d186a63fa812b",
        )
        self.assertEqual(
            research["tree"],
            "7360e366fe8d623ef63ca902c23522bb72935848",
        )
        self.assertEqual(
            research["disposition"], "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED"
        )
        self.assertFalse(research["center_kill_switch_survives"])
        self.assertFalse(research["full_cover_executed"])
        self.assertEqual(research["completed_leaf_count"], 0)
        self.assertEqual(
            research["control_transfer_status"],
            "PATTERN_FALSIFIED_BEFORE_FULL_COVER",
        )

    def test_living_docs_advance_through_203_without_erasing_history(self):
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
                ):
                    self.assertIn(token, text)
                self.assertIn("GLOBAL_MONOTONE_ORIENTATION", text)
                self.assertIn("J_POSITIVE", text)
                self.assertIn("SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED", text)
                self.assertIn("DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED", text)
                self.assertIn("COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED", text)
                self.assertIn("RH remains OPEN", text)

    def test_current_plan_consumes_pair_a_representation_engineering(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "latest merged research PR = #203",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "center_kill_switch_survives = false",
            "full_cover_executed = false",
            "completed_leaf_count = 0",
            "PATTERN_FALSIFIED_BEFORE_FULL_COVER",
            "Pair-A representation engineering = CONSUMED / DOWNGRADED",
            "Pair D — two-parity squeeze = HIGHEST INFORMATION / NEXT RESEARCH ROUTE",
            "Pair B — negative-index separation vs localized critical-line sampling rigidity = SECONDARY",
            "OBS-059",
            "simultaneous even/odd bad exclusion",
            "sourceMoment <-> M4 rigidity",
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
            "PR #203",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "center_kill_switch_survives=false",
            "full_cover_executed=false",
            "completed_leaf_count=0",
            "PATTERN_FALSIFIED_BEFORE_FULL_COVER",
            "Pair D",
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

    def test_validation_protocol_records_falsification_and_rational_conversion_rule(self):
        text = (RHRC / "VALIDATION_PROTOCOL.md").read_text(encoding="utf-8")
        for token in (
            "PR #203",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "SUCCESSFUL FALSIFICATION RESEARCH",
            "exact rational",
            "Integer-only conversion helpers are forbidden",
            "G=O-E",
            "GLOBAL_MONOTONE_ORIENTATION",
            "J_POSITIVE",
            "theorem authority remains #184",
        ):
            self.assertIn(token, text)

    def test_post203_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_203_Q14_COMPOSITE_PARITY_GAP_DELTA.md"
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
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "PATTERN_FALSIFIED_BEFORE_FULL_COVER",
            "GLOBAL_MONOTONE_ORIENTATION",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "Pair D",
            "Pair B",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_obstruction_delta_promotes_obs059_without_overclaim(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_203_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-056",
            "OBS-057",
            "OBS-058",
            "OBS-059",
            "OPEN / ACTIVE / HIGHEST INFORMATION",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "simultaneous even/odd bad exclusion",
            "sourceMoment <-> M4",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_dead_route_delta_blocks_post_hoc_pair_a_rescue(self):
        text = (RHRC / "DEAD_ROUTES_POST_203_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "DR-020",
            "DR-028",
            "COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED",
            "post-hoc",
            "revival requirement",
            "Pair D",
            "Pair B",
            "RH remains OPEN",
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
