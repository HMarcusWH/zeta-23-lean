import json
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace

RHRC = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RHRC))

from control_v2.run_control import _collect_retro_receipts
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

    def test_state_has_post_140_theorem_and_post_117_control_anchors(self):
        state = load_research_state()
        self.assertEqual(state.anchor.pr, 140)
        self.assertEqual(
            state.anchor.merge_commit,
            "fa96196b5bd6ed754853b0bdacee1dbd2356022f",
        )
        self.assertEqual(
            state.anchor.tree,
            "2015404927540ae79a64469af82813463694b71d",
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
            "FIRST_BAD_RIGIDITY_E4_A4R_REGULAR_APERTURE_SELECTION",
        )

    def test_completed_actions_are_not_routable_and_new_actions_are_present(self):
        action_ids = {a.action_id for a in load_actions()}
        self.assertNotIn("E4_A4_KERNEL_SOURCE_TRANSPORT", action_ids)
        self.assertNotIn("E4_A4_ABSOLUTE_SOURCE_ENERGY", action_ids)
        self.assertIn("E4_A4_REGULAR_APERTURE_SELECTION", action_ids)
        self.assertIn("E4_A4_REGULAR_SCHUR_ENERGY_SIGN", action_ids)
        self.assertIn("E4_A4_CANONICAL_ONE_STEP_DOMINATION", action_ids)

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
        self.assertEqual(a.selected_action, "E4_A4_REGULAR_APERTURE_SELECTION")
        self.assertTrue(any(SCORE_FORMULA_VERSION in line for line in a.rationale))
        for action in actions:
            self.assertTrue(any(action.action_id in line for line in a.rationale))

    def test_regular_aperture_action_outranks_domination_and_deformation(self):
        scores = {a.action_id: action_score(a) for a in load_actions()}
        self.assertGreater(
            scores["E4_A4_REGULAR_APERTURE_SELECTION"],
            scores["E4_A4_CANONICAL_ONE_STEP_DOMINATION"],
        )
        self.assertGreater(
            scores["E4_A4_REGULAR_APERTURE_SELECTION"],
            scores["DEFORMATION_BUDGET_PAPER_TEST"],
        )

    def test_regular_aperture_action_is_post140_fixed_cell_finite_horizon(self):
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        action = registry["actions"]["E4_A4_REGULAR_APERTURE_SELECTION"]
        objections = "\n".join(action["surviving_objections"])
        first_breaks = "\n".join(x["statement"] for x in action["first_breaks"])
        self.assertIn("PR #140", objections)
        self.assertIn("frozen cutoff cell", objections)
        self.assertIn("sizes through N", objections)
        self.assertIn("fixed cutoff/parity/size", first_breaks)
        self.assertIn("finite simultaneous avoidance", first_breaks)

    def test_universal_domination_remains_routable_but_is_not_selected(self):
        state = load_research_state()
        actions = load_actions()
        action_ids = {a.action_id for a in actions}
        self.assertIn("E4_A4_CANONICAL_ONE_STEP_DOMINATION", action_ids)
        receipts = {a.action_id: "RETRO-test" for a in actions}
        complete = {a.action_id: True for a in actions}
        first_break_counts = {a.action_id: 1 for a in actions}
        cert = recommend(
            state,
            actions,
            retro_receipts=receipts,
            retro_complete=complete,
            first_break_counts=first_break_counts,
        )
        self.assertNotEqual(cert.selected_action, "E4_A4_CANONICAL_ONE_STEP_DOMINATION")

    def test_regular_schur_sign_is_explicit_future_obligation(self):
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        self.assertIn("E4_A4_REGULAR_SCHUR_ENERGY_SIGN", registry["open_obligations"])
        action = registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]
        self.assertEqual(action["concept_id"], "canonical_source_exclusion")
        self.assertTrue(action["first_break_required"])
        self.assertGreaterEqual(len(action["first_breaks"]), 2)

    def test_shared_retro_concept_is_searched_once_per_run(self):
        actions = load_actions()
        calls: list[str] = []

        def fake_search(**kwargs):
            concept_id = kwargs["concept_id"]
            calls.append(concept_id)
            return SimpleNamespace(
                receipt_id=f"RETRO-{concept_id}",
                search_complete=True,
                searched_sources=(),
            )

        receipts = _collect_retro_receipts(
            actions,
            as_of_ref="anchor",
            archive_root=None,
            exhaustive=True,
            search_fn=fake_search,
        )

        retro_actions = [a for a in actions if a.retro_search_required]
        unique_concepts = {a.concept_id for a in retro_actions}
        self.assertEqual(len(calls), len(unique_concepts))
        self.assertEqual(set(calls), unique_concepts)

        e4a4_ids = (
            "E4_A4_REGULAR_APERTURE_SELECTION",
            "E4_A4_REGULAR_SCHUR_ENERGY_SIGN",
            "E4_A4_CANONICAL_ONE_STEP_DOMINATION",
            "E4_A4_GLOBAL_FIRST_BAD_EXCLUSION",
        )
        self.assertEqual(len({id(receipts[action_id]) for action_id in e4a4_ids}), 1)

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
