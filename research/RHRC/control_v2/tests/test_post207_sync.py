import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post207SyncTests(unittest.TestCase):
    """Preserve the #207 synchronization contract after later theorem anchors advance."""

    def test_current_state_has_advanced_but_preserves_207_history(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertGreaterEqual(state["merged_theorem_anchor"]["pr"], 207)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")
        note = state["control_note"]
        for token in (
            "PR #207",
            "7e186ede13beece95e8a08b2449cd3accbe5b2f5",
            "76cf4e3b5ef4b7ab904a861b6d4cb01fdcd8d0e0",
            "d6509407cc7b667b0ff3e7faab2acd525ae32db9",
            "oddBad_or_sourceMomentMomentFour_re_pos_of_even",
        ):
            self.assertIn(token, note)

    def test_post207_delta_remains_immutable_historical_evidence(self):
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
            "-lam * ||Dv||^2 <= re(star(sourceMoment) * M4)",
            "DERIVED / not yet separately formalized",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_post207_obstruction_delta_remains_historical(self):
        text = (RHRC / "OBSTRUCTION_LEDGER_POST_207_DELTA.md").read_text(encoding="utf-8")
        for token in (
            "OBS-059",
            "FALSIFIED / CONSUMED BY #205",
            "PROVED THROUGH #207",
            "canonical simultaneous odd-bad branch",
            "odd-selected first-bad closure",
            "same-state terminal incompatibility",
            "OBS-059Q",
            "DERIVED LEAD / NOT YET SEPARATELY FORMALIZED",
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_207_sync_did_not_promote_claim_surfaces(self):
        claim_registry = json.loads((RHRC / "CLAIM_REGISTRY.json").read_text(encoding="utf-8"))
        bindings = json.loads((RHRC / "R003_PROMOTED_BINDINGS.json").read_text(encoding="utf-8"))
        registry = json.loads((RHRC / "routes" / "ROUTE_REGISTRY.json").read_text(encoding="utf-8"))
        route = next(r for r in registry["routes"] if r["route_id"] == "R003_ccm_bridge")
        self.assertEqual(route["phase"], "DISCOVERY")
        self.assertFalse(route["confirmatory_execution_authorized"])
        self.assertIsInstance(claim_registry, dict)
        self.assertIsInstance(bindings, dict)

    def test_historical_living_docs_still_contain_207_ancestry(self):
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
                self.assertIn("#207", text)
                self.assertIn("RH remains OPEN", text)


if __name__ == "__main__":
    unittest.main()