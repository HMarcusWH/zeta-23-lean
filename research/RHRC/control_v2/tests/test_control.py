import json
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.run_control import _collect_retro_receipts, _selected_first_break
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

    def test_state_keeps_post_163_theorem_and_post_117_control_anchors(self):
        state = load_research_state()
        self.assertEqual(state.anchor.pr, 163)
        self.assertEqual(
            state.anchor.merge_commit,
            "bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd",
        )
        self.assertEqual(
            state.anchor.tree,
            "c397b3a015ea54e38ecfe626d6e29556fe963839",
        )
        self.assertEqual(state.control_anchor.pr, 117)
        self.assertEqual(
            state.control_anchor.merge_commit,
            "19346f4c00d13bf33db95cbe5325233f86e54c12",
        )
        self.assertNotEqual(state.anchor.merge_commit, state.control_anchor.merge_commit)
        self.assertEqual(state.terminal_claim, "RH_OPEN")
        self.assertEqual(
            state.frontier_id,
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_SCHUR_ENERGY_SIGN",
        )

    def test_control_note_records_post176_research_without_moving_theorem_anchor(self):
        control = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        note = control["control_note"]
        self.assertIn("PR #176", note)
        self.assertIn("c6f53131b91b18aff2a50a6db2ddaa2761e7e5aa", note)
        self.assertIn("96cccf715c02ed2bd4ae58f8362180020ae90854", note)
        self.assertIn("q13/N2/K3/even", note)
        self.assertIn("FIXED_UNIT_METHOD_ACCEPTED", note)
        self.assertIn("six primary Q14 boxes", note)
        self.assertIn("factor-2", note)
        self.assertIn("derivative/stationary discrimination", note)
        self.assertIn("replay-hardening debt", note)
        self.assertIn("PR #117 remains the Control-v2 semantic anchor", note)
        self.assertEqual(control["merged_theorem_anchor"]["pr"], 163)
        self.assertEqual(control["merged_control_anchor"]["pr"], 117)
        self.assertEqual(control["terminal_claim"], "RH_OPEN")

    def test_completed_actions_are_not_routable_and_arithmetic_actions_are_present(self):
        action_ids = {a.action_id for a in load_actions()}
        self.assertNotIn("E4_A4_KERNEL_SOURCE_TRANSPORT", action_ids)
        self.assertNotIn("E4_A4_ABSOLUTE_SOURCE_ENERGY", action_ids)
        self.assertNotIn("E4_A4_REGULAR_APERTURE_SELECTION", action_ids)
        self.assertIn("E4_A4_REGULAR_SCHUR_ENERGY_SIGN", action_ids)
        self.assertIn("E4_A4_CANONICAL_ONE_STEP_DOMINATION", action_ids)
        self.assertIn("E4_A4_GLOBAL_FIRST_BAD_EXCLUSION", action_ids)

    def test_router_is_deterministic_non_authoritative_and_transparent(self):
        state = load_research_state()
        actions = load_actions()
        receipts = {a.action_id: "RETRO-test" for a in actions}
        complete = {a.action_id: True for a in actions}
        first_break_counts = {a.action_id: 1 for a in actions}
        a = recommend(state, actions, retro_receipts=receipts, retro_complete=complete,
                      first_break_counts=first_break_counts)
        b = recommend(state, actions, retro_receipts=receipts, retro_complete=complete,
                      first_break_counts=first_break_counts)
        self.assertEqual(a.to_dict(), b.to_dict())
        self.assertFalse(a.theorem_authority)
        self.assertFalse(a.terminal_claim_change)
        self.assertEqual(a.selected_action, "E4_A4_REGULAR_SCHUR_ENERGY_SIGN")
        self.assertTrue(any(SCORE_FORMULA_VERSION in line for line in a.rationale))
        for action in actions:
            self.assertTrue(any(action.action_id in line for line in a.rationale))

    def test_regular_schur_action_outranks_fallbacks(self):
        scores = {a.action_id: action_score(a) for a in load_actions()}
        self.assertGreater(scores["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"],
                           scores["E4_A4_CANONICAL_ONE_STEP_DOMINATION"])
        self.assertGreater(scores["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"],
                           scores["DEFORMATION_BUDGET_PAPER_TEST"])
        self.assertGreater(scores["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"],
                           scores["E4_B_PARITY_SHIFTED_NULLITY"])

    def test_regular_schur_action_is_post176_fb05_fixed_unit_derivative_route(self):
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        action = registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]
        objections = "\n".join(action["surviving_objections"])
        first_breaks = "\n".join(x["statement"] for x in action["first_breaks"])
        break_ids = [x["id"] for x in action["first_breaks"]]

        for token in (
            "PR #163",
            "PR #165",
            "PR #166",
            "PR #167",
            "PR #168",
            "PR #170",
            "PR #172",
            "PR #174",
            "PR #176",
            "theorem-aligned [W|c] one-step Schur pivot",
            "sign-indefinite",
            "q13->16/N2/K3/even",
            "Delta_2(L)=a(L)d(L)-b(L)^2",
            "Q=13/14/15 subcells",
            "100% UNRESOLVED",
            "scalarization alone does not eliminate canonical interval dependency",
            "FIXED_UNIT_METHOD_ACCEPTED",
            "six frozen primary Q14 boxes",
            "factor-2",
            "Delta_2'",
            "replay-hardening debt",
            "determinant and pivot minima",
            "full physical H1 does not imply H1 for the q-removed background",
            "cancellation ratios around 1e9-1e10",
            "nonzero explicitCanonicalSourceMoment does not imply M4",
            "finite weighted sample sum does not by itself determine the seventh jet",
            "simultaneous even/odd successor badness",
            "odd-selected first-bad branch",
            "global aperture and global minimizing-Schur monotonicity remain quarantined",
            "DR-024",
        ):
            self.assertIn(token, objections)

        self.assertEqual(action["dead_route_matches"], [])
        self.assertEqual(break_ids, ["E4A4-SCHUR-FB-05"])
        self.assertIn("#165-#176", first_breaks)
        self.assertIn("local derivative/stationary law", first_breaks)
        self.assertIn("without restating successor positivity", first_breaks)

        selected_break = _selected_first_break(
            registry, "E4_A4_REGULAR_SCHUR_ENERGY_SIGN"
        )
        self.assertIsNotNone(selected_break)
        self.assertEqual(selected_break["break_id"], "E4A4-SCHUR-FB-05")

    def test_universal_domination_remains_routable_but_is_not_selected(self):
        state = load_research_state()
        actions = load_actions()
        self.assertIn("E4_A4_CANONICAL_ONE_STEP_DOMINATION", {a.action_id for a in actions})
        receipts = {a.action_id: "RETRO-test" for a in actions}
        complete = {a.action_id: True for a in actions}
        cert = recommend(
            state, actions,
            retro_receipts=receipts,
            retro_complete=complete,
            first_break_counts={a.action_id: 1 for a in actions},
        )
        self.assertNotEqual(cert.selected_action, "E4_A4_CANONICAL_ONE_STEP_DOMINATION")

    def test_shared_retro_concept_is_searched_once_per_run(self):
        actions = load_actions()
        calls: list[str] = []

        def fake_search(**kwargs):
            concept_id = kwargs["concept_id"]
            calls.append(concept_id)
            return SimpleNamespace(
                receipt_id=f"RETRO-{concept_id}", search_complete=True, searched_sources=()
            )

        receipts = _collect_retro_receipts(
            actions, as_of_ref="anchor", archive_root=None, exhaustive=True, search_fn=fake_search
        )
        retro_actions = [a for a in actions if a.retro_search_required]
        unique_concepts = {a.concept_id for a in retro_actions}
        self.assertEqual(len(calls), len(unique_concepts))
        self.assertEqual(set(calls), unique_concepts)
        e4a4_ids = (
            "E4_A4_REGULAR_SCHUR_ENERGY_SIGN",
            "E4_A4_CANONICAL_ONE_STEP_DOMINATION",
            "E4_A4_GLOBAL_FIRST_BAD_EXCLUSION",
        )
        self.assertEqual(len({id(receipts[action_id]) for action_id in e4a4_ids}), 1)

    def test_missing_retro_receipts_fail_closed(self):
        state = load_research_state()
        actions = load_actions()
        cert = recommend(state, actions, retro_receipts={}, retro_complete={},
                         first_break_counts={a.action_id: 1 for a in actions})
        self.assertEqual(cert.disposition.value, "ABSTAIN")

    def test_incomplete_retro_receipt_fails_closed(self):
        state = load_research_state()
        actions = load_actions()
        receipts = {a.action_id: "RETRO-quick" for a in actions}
        complete = {a.action_id: False for a in actions}
        cert = recommend(state, actions, retro_receipts=receipts, retro_complete=complete,
                         first_break_counts={a.action_id: 1 for a in actions})
        self.assertEqual(cert.disposition.value, "ABSTAIN")

    def test_score_inputs_are_finite(self):
        for a in load_actions():
            self.assertTrue(abs(action_score(a)) < 1e6)

    def test_terminal_answer_does_not_import_control_v2(self):
        terminal = (RHRC / "runner" / "terminal_answer.py").read_text(encoding="utf-8")
        self.assertNotIn("control_v2", terminal)


if __name__ == "__main__":
    unittest.main()
