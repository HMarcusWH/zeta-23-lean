import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
ROOT = RHRC.parent.parent


class Post235SyncTests(unittest.TestCase):
    """Historical PR #235 provenance must survive after later authority advances."""

    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post235_route_provenance_is_preserved(self):
        route = self.state["active_research_route"]
        self.assertEqual(
            route["post235_source_kernel_forbidden_quadrant"], "PROVED_PR_235"
        )
        self.assertEqual(route["post235_deficit_excess_interface"], "PROVED_PR_235")
        self.assertEqual(
            route["post235_source_kernel_seventh_jet_package"], "PROVED_PR_235"
        )
        self.assertEqual(route["post235_real_phase_collapse"], "PROVED_PR_236")
        self.assertEqual(route["post235_source_kernel_reality"], "PROVED_PR_236")
        self.assertEqual(route["post235_one_real_scalar_reduction"], "PROVED_PR_236")

    def test_post235_delta_documents_are_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_235_SOURCE_KERNEL_QUADRANT_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_235_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_later_authority_is_post237(self):
        theorem = self.state["merged_theorem_anchor"]
        delta = self.state["latest_validated_theorem_delta"]
        self.assertEqual(theorem["pr"], 237)
        self.assertEqual(delta["pr"], 237)
        self.assertEqual(
            self.state["active_research_route"]["next_research_target"],
            "CANONICAL_REAL_NEGATIVE_SHIFT_TRANSFER_GEOMETRY",
        )
        self.assertEqual(
            self.state["active_research_route"]["required_new_information"],
            "CONJUGATION_COMPATIBLE_SHIFTED_RESOLVENT_AND_REAL_TRANSFER_COEFFICIENTS",
        )
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

    def test_current_headings_match_post237(self):
        self.assertEqual(
            (ROOT / "AUDIT.md").read_text(encoding="utf-8").splitlines()[0],
            "# RHRC formal audit — merged theorem authority PR #237; research evidence PR #223",
        )
        self.assertEqual(
            (ROOT / "FORK_NOTES.md").read_text(encoding="utf-8").splitlines()[0],
            "# Fork notes — RHRC current state through merged PR #237",
        )


if __name__ == "__main__":
    unittest.main()
