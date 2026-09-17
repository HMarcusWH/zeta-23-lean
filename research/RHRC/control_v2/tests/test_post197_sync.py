import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post197SyncTests(unittest.TestCase):
    def test_authority_split_preserves_post197_history(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertGreaterEqual(state["merged_theorem_anchor"]["pr"], 184)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")
        note = state["control_note"]
        for token in (
            "PR #184",
            "PR #197",
            "2d936f9764abdfeaa82127d5c834c6c3e429da25",
            "162df6ce8bc13a816937d747f2965bff6764fad0",
            "97f6372a4c7c131006b4abc090c86767b9e99990",
            "GLOBAL_MONOTONE_ORIENTATION",
            "J_POSITIVE",
            "certified_t_fraction=1",
            "global_positive_hull=true",
            "bounded_distinct_aperture_twin_exclusion=true",
            "RH remain OPEN",
        ):
            self.assertIn(token, note)

    def test_living_docs_advance_through_197(self):
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
                for token in ("#184", "#190", "#192", "#193", "#195", "#197"):
                    self.assertIn(token, text)
                self.assertIn("PARTIAL_TRAJECTORY_ORIENTATION", text)
                self.assertIn("63/64", text)
                self.assertIn("GLOBAL_MONOTONE_ORIENTATION", text)
                self.assertIn("RH remains OPEN", text)

    def test_current_plan_closes_residual_span_and_moves_to_mechanism(self):
        text = (RHRC / "CURRENT_RESEARCH_PLAN.md").read_text(encoding="utf-8")
        for token in (
            "GLOBAL_MONOTONE_ORIENTATION",
            "uniform orientation = J_POSITIVE",
            "certified t-fraction = 1",
            "global_positive_hull = true",
            "bounded_distinct_aperture_twin_exclusion = true",
            "OBS-056 CLOSED",
            "OBS-057",
            "J' = o''e - e''o",
            "source-mechanism audit",
            "same frozen Q14 hull",
        ):
            self.assertIn(token, text)
        self.assertIn("PARTIAL_TRAJECTORY_ORIENTATION", text)
        self.assertIn("63/64", text)
        self.assertNotIn("J(L) > 0 on the full inherited Q14 hull                                  OPEN", text)

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
            "PR #197",
            "GLOBAL_MONOTONE_ORIENTATION",
            "global_positive_hull=true",
            "bounded_distinct_aperture_twin_exclusion=true",
            "source-mechanism audit",
            "No claim_ids are changed by this synchronization",
        ):
            self.assertIn(token, note)

    def test_validation_protocol_promotes_evidence_class_not_theorem_authority(self):
        text = (RHRC / "VALIDATION_PROTOCOL.md").read_text(encoding="utf-8")
        for token in (
            "PR #197",
            "GLOBAL_MONOTONE_ORIENTATION",
            "RIGOROUS BOUNDED RESEARCH",
            "certified_t_fraction = 1",
            "global_positive_hull = true",
            "post-#196 / #197 Q14 residual-cell replay regression",
            "theorem authority remains #184",
        ):
            self.assertIn(token, text)

    def test_post197_delta_has_required_post_green_sections(self):
        text = (
            RHRC / "RESEARCH_LEADS_POST_197_Q14_RESIDUAL_CELL_REPLAY_DELTA.md"
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
            "A = J_UNRESOLVED",
            "B = J_POSITIVE",
            "C = J_POSITIVE",
            "certified_t_fraction = 1",
            "global_positive_hull = true",
            "bounded_distinct_aperture_twin_exclusion = true",
            "J' = o''e - e''o",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_obs056_closes_and_obs057_opens(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_197_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-054",
            "OBS-055",
            "OBS-056 CLOSED IN THE FROZEN Q14 RESEARCH SCOPE",
            "OBS-057",
            "GLOBAL_MONOTONE_ORIENTATION",
            "certified_t_fraction = 1",
            "global_positive_hull = true",
            "bounded_distinct_aperture_twin_exclusion = true",
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
