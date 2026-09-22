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

    def test_exact_post243_theorem_authority(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 243)
        self.assertEqual(
            theorem["validated_head"],
            "7b9cc503c50478000ce4ac53c61d4a96ed2d4050",
        )
        self.assertEqual(
            theorem["merge_commit"],
            "be58e98a843ceeceb93a7729d95a3fb6bb0b60df",
        )
        self.assertEqual(
            theorem["tree"],
            "abf8ff5b429adea4adaaec28e182dc30495b1ba8",
        )
        self.assertEqual(delta["pr"], 243)
        self.assertEqual(delta["status"], "MERGED_VIA_PR_243")
        self.assertEqual(
            delta["theorem_family"],
            "OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY",
        )
        self.assertEqual(
            delta["exact_promoted_declaration"],
            "Zeta23.ExceptionalZero."
            "exists_arbitrarilyLarge_wholeCellBiRegular_negativeEnergyCertificate_of_offLine_zero",
        )

    def test_generated_family_is_current_final_gate(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post243_whole_cell_provenance"], "PROVED_PR_243")
        self.assertEqual(
            route["post243_arbitrarily_large_retained_family"], "PROVED_PR_243"
        )
        self.assertEqual(
            route["post243_generated_family_final_gate"],
            "OPEN_EVENTUAL_APERTURE_BOUND",
        )
        self.assertEqual(
            route["post243_candidate_terminal_proposition"],
            "NoArbitrarilyLargeWholeCellRetainedFamily",
        )
        self.assertEqual(route["next_research_target"], "GENERATED_FAMILY_FINAL_GATE")
        self.assertEqual(
            route["required_new_information"],
            "EVENTUAL_CANONICAL_UPPER_BOUND_ON_WHOLE_CELL_RETAINED_APERTURE",
        )
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

    def test_current_headings_match_post243(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #243; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #243",
        )


if __name__ == "__main__":
    unittest.main()
