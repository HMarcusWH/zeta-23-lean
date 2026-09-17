import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post195SyncTests(unittest.TestCase):
    def test_authority_split_preserves_post195_history_while_current_state_advances(self):
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
            "PR #193",
            "TRAJECTORY_RIGIDITY_UNRESOLVED",
            "63/96",
            "33/96",
            "PR #195",
            "ef8af439b4723062061553bfee0ae3eba0205684",
            "380b0011ffa3fac9684ec05496e241b47878be69",
            "cc403fc55454c0f865c17a36d971a9e7947f1a1a",
            "PARTIAL_TRAJECTORY_ORIENTATION",
            "48 J_POSITIVE",
            "48 J_UNRESOLVED",
            "0 H1_UNRESOLVED",
            "63/64",
            "one unresolved span",
            "PR #197",
            "GLOBAL_MONOTONE_ORIENTATION",
            "RH remain OPEN",
        ):
            self.assertIn(token, note)

    def test_living_docs_preserve_195_and_advance_beyond_it(self):
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
                for token in ("#184", "#190", "#192", "#193", "#195"):
                    self.assertIn(token, text)
                self.assertIn("PARTIAL_TRAJECTORY_ORIENTATION", text)
                self.assertIn("63/64", text)
                self.assertIn("#197", text)
                self.assertIn("GLOBAL_MONOTONE_ORIENTATION", text)
                self.assertIn("RH remains OPEN", text)

    def test_current_plan_preserves_post195_partial_history(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "J = o'e - e'o",
            "J' = o''e - e''o",
            "48 J_POSITIVE",
            "48 J_UNRESOLVED",
            "0 J_NEGATIVE",
            "0 H1_UNRESOLVED",
            "one unresolved span",
            "63/64",
            "PARTIAL_TRAJECTORY_ORIENTATION",
            "global_positive_hull = false",
            "bounded_distinct_aperture_twin_exclusion = false",
        ):
            self.assertIn(token, text)
        self.assertIn("#197", text)
        self.assertIn("GLOBAL_MONOTONE_ORIENTATION", text)
        self.assertIn("global_positive_hull = true", text)
        self.assertIn("bounded_distinct_aperture_twin_exclusion = true", text)

    def test_action_registry_preserves_ids_scores_and_post195_evidence(self):
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
        for token in (
            "PR #190",
            "PR #192",
            "PR #193",
            "PR #195",
            "PARTIAL_TRAJECTORY_ORIENTATION",
            "48 J_POSITIVE",
            "48 J_UNRESOLVED",
            "63/64",
            "J'=o''e-e''o",
            "bilinear",
            "cross-channel",
        ):
            self.assertIn(token, objections)

    def test_route_registry_preserves_post195_ancestry_without_claim_id_change(self):
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
            "PR #192",
            "PR #193",
            "PR #195",
            "PARTIAL_TRAJECTORY_ORIENTATION",
            "48 J_POSITIVE",
            "48 J_UNRESOLVED",
            "63/64",
            "global_positive_hull=false",
            "J'=o''e-e''o",
            "No claim_ids are changed by this synchronization",
        ):
            self.assertIn(token, note)

    def test_validation_protocol_preserves_partial_cover_evidence_class(self):
        text = (RHRC / "VALIDATION_PROTOCOL.md").read_text(encoding="utf-8")
        for token in (
            "PR #195",
            "PARTIAL_TRAJECTORY_ORIENTATION",
            "RIGOROUS BOUNDED PARTIAL ORIENTATION RESEARCH",
            "63/64",
            "global_positive_hull = false",
            "J' = o''e - e''o",
            "complete signed Arb interval cover",
        ):
            self.assertIn(token, text)

    def test_post195_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_195_PARITY_TRAJECTORY_SHARP_ENCLOSURE_DELTA.md"
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
            "PARTIAL_TRAJECTORY_ORIENTATION",
            "second_order_h1_recovery_count = 63",
            "representation_conflict_count = 0",
            "unresolved_span_count = 1",
            "certified_t_fraction = 63/64",
            "global_positive_hull = false",
            "bounded_distinct_aperture_twin_exclusion = false",
            "J' = o''e - e''o",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_obs055_narrows_to_obs056_historically(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_195_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-054",
            "OBS-055",
            "OBS-055 NARROWED",
            "OBS-056",
            "48 J_POSITIVE",
            "48 J_UNRESOLVED",
            "0 H1_UNRESOLVED",
            "63/64",
            "PARTIAL_TRAJECTORY_ORIENTATION",
            "does not erase the earlier records",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

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
