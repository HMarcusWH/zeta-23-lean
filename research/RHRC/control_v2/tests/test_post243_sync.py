import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent

class Post243SyncTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post243_theorem_provenance_survives_later_authority(self):
        note = self.state["control_note"]
        for token in (
            "PR #243",
            "7b9cc503c50478000ce4ac53c61d4a96ed2d4050",
            "be58e98a843ceeceb93a7729d95a3fb6bb0b60df",
            "abf8ff5b429adea4adaaec28e182dc30495b1ba8",
            "arbitrarily large retained aperture",
        ):
            self.assertIn(token, note)
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 247)
        self.assertEqual(self.state["latest_validated_theorem_delta"]["prior_theorem_authority_pr"], 246)

    def test_generated_family_gate_is_preserved_as_historical_rh_equivalent(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post243_whole_cell_provenance"], "PROVED_PR_243")
        self.assertEqual(route["post243_arbitrarily_large_retained_family"], "PROVED_PR_243")
        self.assertEqual(route["post245_generated_family_final_gate"], "RH_EQUIVALENT_PR_245")
        self.assertEqual(route["post243_contact_route_role"], "FALLBACK_ONLY")
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_post243_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for p in (
            RHRC / "RESEARCH_LEADS_POST_243_GENERATED_FAMILY_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_243_DELTA.md",
        ):
            text = p.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_current_headings_match_post247(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #247; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #247",
        )

if __name__ == "__main__":
    unittest.main()
