import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post233SyncTests(unittest.TestCase):
    """Historical PR #233 theorem state must remain represented after later advances."""

    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post233_route_provenance_is_preserved(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post233_good_sector_gram"], "PROVED_PR_233")
        self.assertEqual(route["post233_shifted_resolvent_energy"], "PROVED_PR_233")
        self.assertEqual(route["post233_retained_source_gram_disk"], "PROVED_PR_233")
        self.assertEqual(route["post233_sharp_negative_shift_disk"], "PROVED_PR_233")
        self.assertEqual(route["post233_disk_emptiness"], "OPEN_NOT_PROVED")
        self.assertEqual(
            route["good_sector_one_step_domination_independence"],
            "CONSUMED_NOT_INDEPENDENT_PR_233",
        )

    def test_post233_delta_documents_remain_complete(self):
        required_sections = (
            "What became formally true",
            "Workflow harvest",
            "What changed",
            "Upstream implications",
            "Downstream implications",
            "Resurrected routes",
            "New RH-relevant clues",
            "Falsification checks",
            "Highest-leverage next moves",
            "Standing questions",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_233_GRAM_DISK_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_233_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_later_authority_does_not_mutate_control_semantics(self):
        self.assertEqual(self.state["merged_theorem_anchor"]["pr"], 237)
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")


if __name__ == "__main__":
    unittest.main()
