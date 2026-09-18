import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post209SyncTests(unittest.TestCase):
    """Preserve the #209 synchronization contract after later theorem anchors advance."""

    def test_current_state_has_advanced_but_preserves_209_history(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertGreaterEqual(state["merged_theorem_anchor"]["pr"], 209)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")
        note = state["control_note"]
        for token in (
            "PR #209",
            "a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392",
            "e029af769e01a547ebbc6ed045509bb2cbdd6cff",
            "6a75278ebf3f2bd19a77419238872cb81835ec13",
            "oddBad_or_sourceMomentMixedJet_re_neg_of_even",
            "evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad",
            "OBS-059Q is CLOSED / PROVED BY #209",
        ):
            self.assertIn(token, note)

    def test_post209_delta_remains_immutable_historical_evidence(self):
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
            "RH remains OPEN",
        ):
            self.assertIn(token, text)

    def test_post209_obstruction_delta_remains_historical(self):
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

    def test_historical_living_docs_still_contain_209_ancestry(self):
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
                self.assertIn("#209", text)
                self.assertIn("RH remains OPEN", text)

    def test_209_sync_did_not_promote_claim_surfaces(self):
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
