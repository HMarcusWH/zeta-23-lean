import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post201SyncTests(unittest.TestCase):
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
        note = state["control_note"]
        for token in (
            "PR #201",
            "be5b98dfce12777436bc40b39a37b04669ae4311",
            "319db6f68f65bdcffc0657c03bea76502da59a57",
            "840a2e8b0bf690507bc3385fbe122210e6d32c7a",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "paired_source_sum_positive_leaf_count=0",
            "paired_source_sum_unresolved_leaf_count=49",
            "NO_UNIQUE_PRIMARY_LOCK",
            "GLOBAL_MONOTONE_ORIENTATION",
            "J_POSITIVE",
            "RH remains OPEN",
        ):
            self.assertIn(token, note)

    def test_living_docs_advance_through_201(self):
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
                ):
                    self.assertIn(token, text)
                self.assertIn("GLOBAL_MONOTONE_ORIENTATION", text)
                self.assertIn("SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED", text)
                self.assertIn("DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED", text)
                self.assertIn("RH remains OPEN", text)

    def test_current_plan_consumes_discrepancy_first_lane(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "latest merged research PR = #201",
            "uniform orientation = J_POSITIVE",
            "certified t-fraction = 1",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "paired source sums positive = 0/49",
            "paired source sums unresolved = 49/49",
            "OBS-057 OPEN / FURTHER NARROWED",
            "OBS-058 OPEN / NARROWED THROUGH #201",
            "stop source chopping",
            "full-composite parity-gap mechanism",
            "exact-center kill-switch",
            "Pair D",
            "Pair B",
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
            "PR #201",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "GLOBAL_MONOTONE_ORIENTATION",
            "J_POSITIVE",
            "full-composite",
            "six-center kill-switch",
            "Pair D / Pair B",
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
        self.assertEqual(action["score_inputs"]["information_gain"], 5.0)
        self.assertEqual([b["id"] for b in action["first_breaks"]], ["E4A4-SCHUR-FB-05"])

    def test_validation_protocol_separates_paired_nonresolution_from_direct_sign(self):
        text = (RHRC / "VALIDATION_PROTOCOL.md").read_text(encoding="utf-8")
        for token in (
            "PR #201",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "representation limitation, not sign reversal",
            "GLOBAL_MONOTONE_ORIENTATION",
            "RIGOROUS BOUNDED RESEARCH",
            "theorem authority remains #184",
            "0/49",
        ):
            self.assertIn(token, text)

    def test_post201_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_201_Q14_DISCREPANCY_MECHANISM_DELTA.md"
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
            "GLOBAL_MONOTONE_ORIENTATION",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "paired_source_sum_positive_leaf_count = 0",
            "paired_source_sum_unresolved_leaf_count = 49",
            "J_DD",
            "J_DA",
            "J_AA",
            "full-composite",
            "Pair D",
            "Pair B",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_obstruction_delta_narrows_obs057_and_obs058(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_201_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-056",
            "OBS-057",
            "OPEN / FURTHER NARROWED",
            "OBS-058",
            "OPEN / NARROWED THROUGH #201",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED",
            "D = pole + prime_signed",
            "full-composite",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_dr020_records_post201_regrouping_warning(self):
        text = (RHRC / "DEAD_ROUTES.md").read_text(encoding="utf-8")
        self.assertIn("DR-020", text)
        self.assertIn("Post-#199 clarification", text)
        self.assertIn("Post-#201 clarification", text)
        self.assertIn("SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED", text)
        self.assertIn("DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED", text)
        self.assertIn("linear source regrouping", text)

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
