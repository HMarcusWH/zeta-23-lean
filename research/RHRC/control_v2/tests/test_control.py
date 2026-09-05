import json
import sys
import unittest
from pathlib import Path

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.router import SCORE_FORMULA_VERSION, action_score, load_actions, recommend
from control_v2.state import load_research_state


class ControlV2Tests(unittest.TestCase):
    def test_control_boundary_has_no_claim_authority(self):
        boundary = json.loads((RHRC / "control_v2" / "CONTROL_BOUNDARY.json").read_text())
        self.assertFalse(boundary["may_write_claim_registry"])
        self.assertFalse(boundary["may_write_boundary"])
        self.assertFalse(boundary["may_write_route_registry"])
        self.assertFalse(boundary["may_emit_terminal_rh_status"])
        self.assertFalse(boundary["may_promote_lean_theorem"])

    def test_state_has_separate_post_115_theorem_and_post_116_control_anchors(self):
        state = load_research_state()
        self.assertEqual(state.anchor.pr, 115)
        self.assertEqual(state.control_anchor.pr, 116)
        self.assertNotEqual(state.anchor.merge_commit, state.control_anchor.merge_commit)
        self.assertEqual(state.terminal_claim, "RH_OPEN")
        self.assertEqual(state.frontier_id, "FIRST_BAD_RIGIDITY_E2")

    def test_router_is_deterministic_non_authoritative_and_transparent(self):
        state = load_research_state()
        actions = load_actions()
        receipts = {a.action_id: "RETRO-test" for a in actions}
        complete = {a.action_id: True for a in actions}
        first_break_counts = {a.action_id: 1 for a in actions}
        a = recommend(
            state,
            actions,
            retro_receipts=receipts,
            retro_complete=complete,
            first_break_counts=first_break_counts,
        )
        b = recommend(
            state,
            actions,
            retro_receipts=receipts,
            retro_complete=complete,
            first_break_counts=first_break_counts,
        )
        self.assertEqual(a.to_dict(), b.to_dict())
        self.assertFalse(a.theorem_authority)
        self.assertFalse(a.terminal_claim_change)
        self.assertIsNotNone(a.selected_action)
        self.assertTrue(any(SCORE_FORMULA_VERSION in line for line in a.rationale))
        for action in actions:
            self.assertTrue(any(action.action_id in line for line in a.rationale))

    def test_missing_retro_receipts_fail_closed(self):
        state = load_research_state()
        actions = load_actions()
        cert = recommend(
            state,
            actions,
            retro_receipts={},
            retro_complete={},
            first_break_counts={a.action_id: 1 for a in actions},
        )
        self.assertEqual(cert.disposition.value, "ABSTAIN")

    def test_incomplete_retro_receipt_fails_closed(self):
        state = load_research_state()
        actions = load_actions()
        receipts = {a.action_id: "RETRO-quick" for a in actions}
        complete = {a.action_id: False for a in actions}
        cert = recommend(
            state,
            actions,
            retro_receipts=receipts,
            retro_complete=complete,
            first_break_counts={a.action_id: 1 for a in actions},
        )
        self.assertEqual(cert.disposition.value, "ABSTAIN")

    def test_score_inputs_are_finite(self):
        for action in load_actions():
            self.assertTrue(abs(action_score(action)) < 1e6)

    def test_terminal_answer_does_not_import_control_v2(self):
        terminal = (RHRC / "runner" / "terminal_answer.py").read_text(encoding="utf-8")
        self.assertNotIn("control_v2", terminal)


if __name__ == "__main__":
    unittest.main()
