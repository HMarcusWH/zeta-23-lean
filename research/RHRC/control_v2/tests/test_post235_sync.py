import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post235SyncTests(unittest.TestCase):
    """Historical PR #235 theorem state must remain represented after later advances."""

    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post235_route_provenance_is_preserved(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post235_source_kernel_forbidden_quadrant"], "PROVED_PR_235")
        self.assertEqual(route["post235_deficit_excess_interface"], "PROVED_PR_235")
        self.assertEqual(route["post235_source_kernel_seventh_jet_package"], "PROVED_PR_235")
        self.assertEqual(route["post235_real_phase_collapse"], "PROVED_PR_236")
        self.assertEqual(route["post235_source_kernel_reality"], "PROVED_PR_236")
        self.assertEqual(route["post235_one_real_scalar_reduction"], "PROVED_PR_236")

    def test_post235_delta_documents_remain_complete(self):
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

    def test_later_authority_does_not_mutate_control_semantics(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 236)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")


if __name__ == "__main__":
    unittest.main()
