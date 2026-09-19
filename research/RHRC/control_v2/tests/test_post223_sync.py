import json
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
STATE = ROOT / "research/RHRC/control_v2/CONTROL_STATE.json"


class Post223SyncTests(unittest.TestCase):
    def test_post223_research_evidence_is_frozen(self):
        state = json.loads(STATE.read_text())
        research = state["latest_research_evidence"]
        self.assertEqual(research["pr"], 223)
        self.assertEqual(research["validated_head"], "5e01e55544be937b0f0e389f1f279e13a89f2b3a")
        self.assertEqual(research["merge_commit"], "8c57ce445a2223dab4a3e8aedbd3db67171e96b0")
        self.assertEqual(research["tree"], "3588cd964a3346b20e359b41c02eb8caaed3221a")
        self.assertEqual(
            research["disposition"],
            "NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED",
        )
        self.assertEqual(research["qualified_cell_minimal_point_count"], 0)
        self.assertEqual(research["evidence_class"], "RIGOROUS_BOUNDED_ARB_RESEARCH")
        self.assertFalse(research["theorem_promotion"])

    def test_post223_did_not_promote_theorem_or_close_route(self):
        state = json.loads(STATE.read_text())
        self.assertEqual(state["merged_theorem_anchor"]["pr"], 222)
        self.assertEqual(state["merged_control_anchor"]["pr"], 117)
        self.assertEqual(state["active_research_route"]["active_subobligation"], "OBS-059I")
        self.assertEqual(state["terminal_claim"], "RH_OPEN")


if __name__ == "__main__":
    unittest.main()
