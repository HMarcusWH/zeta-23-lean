import json
import unittest
from pathlib import Path


RHRC = Path(__file__).resolve().parents[2]


class Post186SyncTests(unittest.TestCase):
    def test_control_state_keeps_theorem_and_control_anchors_fixed(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        self.assertEqual(state["merged_theorem_anchor"]["pr"], 184)
        self.assertEqual(
            state["merged_theorem_anchor"]["merge_commit"],
            "6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e",
        )
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["terminal_claim"], "RH_OPEN")

    def test_control_note_records_post186_mixed_research_without_promotion(self):
        state = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        note = state["control_note"]
        for token in (
            "PR #186",
            "7d277a99437d98fdb7c831f25a130eac07f1b3af",
            "0494658a87d29eeb2124aa16232c264c21d23c18",
            "RHRC #1091",
            "Permansson #864",
            "DOMINATION_SIGNAL_MIXED",
            "det_left_o2^-10_r2^-13",
            "det_left_o2^-13_r2^-16",
            "det_right_o2^-10_r2^-13",
            "det_right_o2^-13_r2^-16",
            "det_left_o2^-16_r2^-19",
            "det_right_o2^-16_r2^-19",
            "FINITE_WIDTH_OUT_OF_H1_SCOPE",
            "simple universal production-remainder domination formulation is falsified",
            "PR #184 remains valid",
            "sign-neutral theorem infrastructure",
            "RH remain OPEN",
        ):
            self.assertIn(token, note)

    def test_living_docs_advance_research_anchor_to_186(self):
        paths = (
            RHRC / "DOCUMENTATION_AUTHORITY.md",
            RHRC / "CURRENT_RESEARCH_PLAN.md",
            RHRC / "RESEARCH_LEADS.md",
            RHRC / "routes" / "R003_ccm_bridge" / "README.md",
        )
        for path in paths:
            text = path.read_text(encoding="utf-8")
            with self.subTest(path=path):
                self.assertIn("#186", text)
                self.assertIn("DOMINATION_SIGNAL_MIXED", text)
                self.assertIn("#184", text)
                self.assertIn("RH remains OPEN", text)

    def test_post186_delta_has_required_post_green_sections(self):
        delta = (
            RHRC / "RESEARCH_LEADS_POST_186_REMAINDER_DRIFT_MIXED_DELTA.md"
        ).read_text(encoding="utf-8")
        for heading in (
            "# What became formally true",
            "# What became research-certified",
            "# What changed",
            "# Upstream implications",
            "# Downstream implications",
            "# Resurrected routes",
            "# New RH-relevant clues",
            "# Falsification checks",
            "# Highest-leverage next moves",
            "# Standing questions",
        ):
            self.assertIn(heading, delta)
        self.assertIn("DOMINATION_SIGNAL_MIXED", delta)
        self.assertIn("theorem promotion", delta)
        self.assertIn("RH remains OPEN", delta)


if __name__ == "__main__":
    unittest.main()
