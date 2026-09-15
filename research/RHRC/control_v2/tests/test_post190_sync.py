import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]


class Post190SyncTests(unittest.TestCase):
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
            "PR #190",
            "8701920b0da18ae6595ad0eee55c1f6cb291a94f",
            "f87da9fde71dd1e74419c6ae5848eee3787c27e4",
            "af8774b65c898de221a5bf32977ccff3407a7b2d",
            "RHRC #1096",
            "Permansson #869",
            "JOINT_EXACT_VECTOR_SEPARABLE",
            "JOINT_THRESHOLD_SIGNATURE_SEPARABLE",
            "all 127 nonempty subsets",
            "canonical-production realizability audit",
            "scalar_shift=2*cCorrection'(L) I",
            "arch_signed=-arch_direct-scalar_shift",
            "PR #117 remains the Control-v2 semantic anchor",
            "RH remain OPEN",
        ):
            self.assertIn(token, note)

    def test_living_docs_advance_to_post190_realizability_frontier(self):
        paths = (
            RHRC.parent.parent / "README.md",
            RHRC.parent.parent / "AUDIT.md",
            RHRC.parent.parent / "FORK_NOTES.md",
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
                self.assertIn("#190", text)
                self.assertIn("#184", text)
                self.assertIn("canonical", text.lower())
                self.assertIn("realiz", text.lower())
                self.assertIn("RH remains OPEN", text)
                self.assertNotIn("latest merged research PR = #186", text)

    def test_current_plan_consumes_frozen_selector_composition(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "STOP searching combinations/refits of G1/P1/P2/C1-C4",
            "all 127 nonempty subsets",
            "canonical production realizability",
            "Layer 0",
            "Layer 5",
            "EXACT_TWIN_SURVIVES",
            "EXACT_TWIN_EXCLUDED_BY_IDENTITY",
            "UNRESOLVED",
        ):
            self.assertIn(token, text)

    def test_action_registry_keeps_ids_scores_and_reroutes_first_break(self):
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
        objections = "\n".join(action["surviving_objections"])
        first_break = action["first_breaks"][0]["statement"]
        for token in (
            "PR #186",
            "PR #188",
            "PR #189",
            "PR #190",
            "all 127 nonempty subsets",
            "canonical production realizability",
            "source-channel construction coupling",
            "scalar-aperture law",
            "same-L/same-Q/same-parity",
        ):
            self.assertIn(token, objections)
        self.assertIn("#186-#190", first_break)
        self.assertIn("ambient normalized algebra", first_break)
        self.assertIn("same retained first-bad/contact state", first_break)

    def test_route_registry_advances_r003_without_claim_id_change_semantics(self):
        registry = json.loads(
            (RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8")
        )
        route = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])
        note = route["note"]
        for token in (
            "PR #184",
            "PR #190",
            "JOINT_EXACT_VECTOR_SEPARABLE",
            "JOINT_THRESHOLD_SIGNATURE_SEPARABLE",
            "all 127 nonempty subsets",
            "canonical-production realizability audit",
            "No claim_ids are changed by this synchronization",
        ):
            self.assertIn(token, note)

    def test_retro_aliases_include_post190_vocabulary_without_generic_noise(self):
        aliases = json.loads(
            (RHRC / "control_v2" / "retro" / "CONCEPT_ALIAS_MAP.json").read_text(
                encoding="utf-8"
            )
        )
        terms = aliases["canonical_source_exclusion"]
        for term in (
            "mixed drift selector",
            "selector semantic independence",
            "joint selector separability",
            "strong selector vector",
            "ambient normalized algebra",
            "smooth channel sign reflection",
            "canonical production realizability",
            "common aperture production state",
            "arch scalar coupling",
            "same-L canonical source reconstruction",
        ):
            self.assertIn(term, terms)
        for generic in ("selector", "reflection", "realizable", "trajectory"):
            self.assertNotIn(generic, terms)

    def test_post190_delta_has_required_post_green_sections(self):
        delta = (
            RHRC / "RESEARCH_LEADS_POST_190_JOINT_SELECTOR_SEPARABILITY_DELTA.md"
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
            self.assertIn(heading, delta)
        for token in (
            "JOINT_EXACT_VECTOR_SEPARABLE",
            "JOINT_THRESHOLD_SIGNATURE_SEPARABLE",
            "127",
            "canonical production realizability",
            "RH remains OPEN",
        ):
            self.assertIn(token, delta)

    def test_post190_obstruction_closes_ambient_selector_sufficiency_only(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_190_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-054",
            "frozen strong-selector composition is insufficient",
            "127",
            "canonical arithmetic realizability",
            "EXACT EXECUTABLE",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)


if __name__ == "__main__":
    unittest.main()
