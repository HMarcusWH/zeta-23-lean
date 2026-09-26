import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]


class Post231SyncTests(unittest.TestCase):
    """Historical PR #231 provenance must remain represented after later theorem advances."""

    def setUp(self):
        self.state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )

    def test_post231_route_provenance_is_preserved(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post231_correction_source_coupling"], "PROVED_PR_231")
        self.assertEqual(route["post231_source_channel_rewrite"], "PROVED_PR_231")
        self.assertEqual(route["post231_gamma_shell_balance"], "PROVED_PR_231")
        self.assertEqual(route["post231_retained_source_balance_factored"], "PROVED_PR_231")
        self.assertEqual(
            route["post231_retained_source_balance_source_nonzero"], "PROVED_PR_231"
        )
        self.assertEqual(route["post231_retained_source_balance_odd_good"], "PROVED_PR_231")
        self.assertEqual(route["post231_source_coupling_sign"], "OPEN_NO_SIGN_PROVED")
        self.assertEqual(route["post231_alpha_reality_sign"], "OPEN_MIXED_RESOLVENT_PAIRING")
        self.assertEqual(route["post231_retained_source_gram_disk"], "PROVED_PR_233")

    def test_post231_delta_documents_remain_complete(self):
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
            RHRC / "RESEARCH_LEADS_POST_231_SOURCE_BALANCE_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_231_DELTA.md",
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
