import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]

class Post229HistoricalRegressionTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_post229_history_is_preserved_after_later_theorem_authority(self):
        self.assertGreater(self.state["merged_theorem_anchor"]["pr"], 229)
        self.assertGreater(self.state["latest_validated_theorem_delta"]["pr"], 229)
        route = self.state["active_research_route"]
        self.assertEqual(route["post229_correction_functional_riesz"], "PROVED_PR_229")
        self.assertEqual(route["post229_alpha_mixed_resolvent_formula"], "PROVED_PR_229")
        self.assertEqual(route["post229_gamma_mixed_resolvent_formula"], "PROVED_PR_229")
        self.assertEqual(route["post229_alpha_reality_sign"], "OPEN_MIXED_RESOLVENT_PAIRING")
        self.assertEqual(route["post229_source_coupling_bridge"], "PROVED_PR_231")
        self.assertEqual(route["post229_retained_source_balance"], "PROVED_PR_231")
        note = self.state["control_note"]
        for token in (
            "PR #229",
            "9d4f81c171264be424fbac40f1211263c3cc6abd",
            "992398c810de5fb84919846fc4192d709d51e783",
            "d9ae07d1ca92cb23b4a3ae3ccae0b32e9b7d38c8",
            "oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div",
            "one_sub_crossParitySecularAlpha_eq_resolvent_pairing_div",
            "one_sub_crossParitySecularGamma_eq_resolvent_pairing_div",
        ):
            self.assertIn(token, note)

    def test_post229_delta_documents_remain_frozen_and_complete(self):
        required_sections = (
            "What became formally true", "Workflow harvest", "What changed",
            "Upstream implications", "Downstream implications", "Resurrected routes",
            "New RH-relevant clues", "Falsification checks", "Highest-leverage next moves",
        )
        for path in (
            RHRC / "RESEARCH_LEADS_POST_229_RIESZ_DELTA.md",
            RHRC / "OBSTRUCTION_LEDGER_POST_229_DELTA.md",
        ):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)
            bad = [(i, ord(ch)) for i, ch in enumerate(text)
                   if (ord(ch) < 32 and ch not in "\n\r") or ord(ch) == 127]
            self.assertEqual(bad, [])

    def test_post229_is_historical_not_current(self):
        self.assertEqual(self.state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(self.state["latest_research_evidence"]["pr"], 223)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

if __name__ == "__main__":
    unittest.main()
