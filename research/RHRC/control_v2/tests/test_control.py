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

    def test_state_has_post_157_theorem_and_post_117_control_anchors(self):
        state = load_research_state()
        self.assertEqual(state.anchor.pr, 157)
        self.assertEqual(
            state.anchor.merge_commit,
            "e304f07c9e83165ebf066db0d67c2cc24f8961c2",
        )
        self.assertEqual(
            state.anchor.tree,
            "706dfde7f9e7b0b8403a671769d424ac7862f5e7",
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
        self.assertEqual(a.selected_action, "E4_A4_REGULAR_SCHUR_ENERGY_SIGN")
        self.assertTrue(any(SCORE_FORMULA_VERSION in line for line in a.rationale))
        for action in actions:
            self.assertTrue(any(action.action_id in line for line in a.rationale))

    def test_regular_schur_action_outranks_fallbacks(self):
        scores = {a.action_id: action_score(a) for a in load_actions()}
        self.assertGreater(
            scores["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"],
            scores["E4_A4_CANONICAL_ONE_STEP_DOMINATION"],
        )
        self.assertGreater(
            scores["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"],
            scores["DEFORMATION_BUDGET_PAPER_TEST"],
        )
        self.assertGreater(
            scores["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"],
            scores["E4_B_PARITY_SHIFTED_NULLITY"],
        )

    def test_regular_schur_action_is_post157_transformed_arithmetic_route(self):
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        action = registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]
        objections = "\n".join(action["surviving_objections"])
        first_breaks = "\n".join(x["statement"] for x in action["first_breaks"])
        break_ids = [x["id"] for x in action["first_breaks"]]

        self.assertIn("PR #157", objections)
        self.assertIn("complex production D-transport", objections)
        self.assertIn("retained Riesz negativity", objections)
        self.assertIn("pointwise fixed-sign", objections)
        self.assertIn("DR-024", objections)
        self.assertIn("seventh/ninth leading-jet formulas", objections)
        # DR-024 kills only a shortcut; the surviving complete-residual route is
        # not reviving it, so Control-v2 must not require a RevivalRecord.
        self.assertEqual(action["dead_route_matches"], [])
        self.assertNotIn("E4A4-SCHUR-FB-01", break_ids)
        self.assertNotIn("E4A4-SCHUR-FB-02", break_ids)
        self.assertNotIn("E4A4-SCHUR-FB-03", break_ids)
        self.assertNotIn("E4A4-SCHUR-FB-03E", break_ids)
        self.assertNotIn("E4A4-SCHUR-FB-03F", break_ids)
        self.assertEqual(
            break_ids,
            [
                "E4A4-SCHUR-FB-04",
                "E4A4-SCHUR-FB-05",
            ],
        )
        self.assertIn("#157 production Riesz", first_breaks)
        self.assertIn("interval-certified", first_breaks)
        self.assertIn("complete-residual", first_breaks)

        selected_break = _selected_first_break(
            registry, "E4_A4_REGULAR_SCHUR_ENERGY_SIGN"
        )
        self.assertIsNotNone(selected_break)
        self.assertEqual(selected_break["break_id"], "E4A4-SCHUR-FB-04")

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
