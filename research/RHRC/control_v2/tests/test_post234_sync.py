import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post234SyncTests(unittest.TestCase):
    """Historical PR #234 theorem state must remain represented after later advances."""

    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post234_route_provenance_is_preserved(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post234_disk_secular_intersection"], "PROVED_PR_234")
        self.assertEqual(route["post234_m4_elimination"], "PROVED_PR_234")
        self.assertEqual(route["post234_source_real_radius_dichotomy"], "PROVED_PR_234")
        self.assertEqual(
            route["post234_numerical_prerequisite"],
            "CANONICAL_CUBIC_SHELL_NORMALIZATION",
        )
        self.assertEqual(
            route["post234_latest_shifted_state_scout"],
            "672_ATTEMPTED_0_SHIFTED_STATES",
        )
        self.assertEqual(route["post234_disk_halfplane_emptiness"], "OPEN_NOT_PROVED")

    def test_post234_delta_documents_remain_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications",
            "Resurrected routes", "New RH-relevant clues",
            "Falsification checks", "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_234_DISK_SECULAR_INTERSECTION_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_234_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_later_authority_does_not_mutate_control_semantics(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 269)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")


if __name__ == "__main__":
    unittest.main()
