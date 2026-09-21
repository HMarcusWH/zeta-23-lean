import json
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]

class Post227HistoricalRegressionTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads((RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8"))

    def test_post227_history_is_preserved_after_later_theorem_authority(self):
        route = self.state["active_research_route"]
        self.assertEqual(route["post227_safe_negative_shift_one_coefficient_transfer"], "PROVED_PR_227")
        self.assertEqual(route["post227_zero_shift_one_coefficient_transfer"], "PROVED_PR_227")
        self.assertEqual(route["post227_kernel_direction_collapse"], "PROVED_PR_227")
        self.assertEqual(route["post227_biregular_selected_even_normal_form"], "PROVED_PR_227")
        note = self.state["control_note"]
        for token in ("PR #227","b8d29733167a95e16f5721eddfced6b650a3b641","7aace87a5644f837e2c8b64bdcf5e66b2dc0b020","crossParitySecularGamma_eq_one_add_kappa_mul_one_sub_alpha"):
            self.assertIn(token, note)

    def test_post227_delta_documents_remain_complete(self):
        required_sections = ("What became formally true","What changed","Upstream implications","Downstream implications","Resurrected routes","New RH-relevant clues","Falsification checks","Highest-leverage next moves")
        for path in (RHRC / "RESEARCH_LEADS_POST_227_ONE_COEFFICIENT_TRANSFER_DELTA.md", RHRC / "OBSTRUCTION_LEDGER_POST_227_DELTA.md"):
            text = path.read_text(encoding="utf-8")
            for section in required_sections:
                self.assertIn(section, text)

    def test_post227_is_historical_not_current(self):
        self.assertGreater(self.state["merged_theorem_anchor"]["pr"], 227)
        self.assertGreater(self.state["latest_validated_theorem_delta"]["pr"], 227)
        self.assertEqual(self.state["terminal_claim"], "RH_OPEN")

if __name__ == "__main__":
    unittest.main()
