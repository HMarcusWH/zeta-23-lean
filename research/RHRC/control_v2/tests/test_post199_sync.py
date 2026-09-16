import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post199SyncTests(unittest.TestCase):
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
            "PR #199",
            "fabe301c95277345f0efe764252ce1c1213a4112",
            "27dda545b7ccdb2870088ebaf317d85e3d999555",
            "85eb8ea25d240c4a9c339262bdc611fae881f7f0",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "NO_UNIQUE_COLLAPSED_UNIFORM_LOCK",
            "GLOBAL_MONOTONE_ORIENTATION",
            "J_POSITIVE",
            "RH remain OPEN",
        ):
            self.assertIn(token, note)

    def test_living_docs_advance_through_199(self):
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
                for token in ("#184", "#190", "#192", "#193", "#195", "#197", "#199"):
                    self.assertIn(token, text)
                self.assertIn("GLOBAL_MONOTONE_ORIENTATION", text)
                self.assertIn("SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED", text)
                self.assertIn("RH remains OPEN", text)

    def test_current_plan_preserves_direct_sign_and_retargets_representation(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "GLOBAL_MONOTONE_ORIENTATION",
            "uniform orientation = J_POSITIVE",
            "certified t-fraction = 1",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "NO_UNIQUE_COLLAPSED_UNIFORM_LOCK",
            "OBS-057 OPEN / NARROWED",
            "OBS-058 OPEN",
            "D = pole + prime_signed",
            "A = direct_arch_signed",
            "cancellation-preserving",
            "source-mechanism audit",
            "same frozen Q14 hull",
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
            "PR #199",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "GLOBAL_MONOTONE_ORIENTATION",
            "J_POSITIVE",
            "D=pole+prime_signed",
            "A=direct_arch_signed",
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

    def test_validation_protocol_keeps_decomposition_nonresolution_separate_from_direct_sign(self):
        text = (RHRC / "VALIDATION_PROTOCOL.md").read_text(encoding="utf-8")
        for token in (
            "PR #199",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "representation limitation, not sign reversal",
            "GLOBAL_MONOTONE_ORIENTATION",
            "RIGOROUS BOUNDED RESEARCH",
            "theorem authority remains #184",
        ):
            self.assertIn(token, text)

    def test_post199_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_199_Q14_SOURCE_DECOMPOSITION_DELTA.md"
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
            "D = pole + prime_signed",
            "A = direct_arch_signed",
            "J_DD",
            "J_DA",
            "J_AA",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_obstruction_delta_narrows_obs057_and_opens_obs058(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_199_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-056",
            "OBS-057",
            "OPEN / NARROWED",
            "OBS-058",
            "OPEN / ACTIVE RESEARCH OBSTRUCTION",
            "SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED",
            "D = pole + prime_signed",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_dr020_records_post199_representation_warning(self):
        text = (RHRC / "DEAD_ROUTES.md").read_text(encoding="utf-8")
        self.assertIn("DR-020", text)
        self.assertIn("Post-#199 clarification", text)
        self.assertIn("SOURCE_DECOMPOSITION_DEPENDENCY_UNRESOLVED", text)
        self.assertIn("pole-prime discrepancy", text)

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
