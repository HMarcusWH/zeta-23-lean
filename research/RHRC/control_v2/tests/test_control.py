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
    def test_control_state_tracks_latest_theorem_anchor_without_moving_control_anchor(self):
        state = load_research_state()
        self.assertEqual(state.anchor.pr, 211)
        self.assertEqual(
            state.anchor.merge_commit,
            "dd42e6368e48957c9922a9e917e10f60a2582b9f",
        )
        self.assertEqual(
            state.anchor.tree,
            "a735f6149aeaa9f8358394c33fd6dcee8062f68e",
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

    def test_control_note_preserves_history_and_records_post211_theorem(self):
        control = json.loads(
            (RHRC / "control_v2" / "CONTROL_STATE.json").read_text(encoding="utf-8")
        )
        note = control["control_note"]
        for token in (
            "PR #184",
            "a756494ebe7e2530715e996b9a9a341fbe07c683",
            "6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e",
            "6c77cd470809959a403b3bcc5f08d39f4076fa4c",
            "complex-Hermitian",
            "M~(t)=-tI+R~(t)",
            "P_t'=-envelopeNormSq+remainderEnvelopeDerivative",
            "PR #180",
            "a87469da9e611b53ae400cb4b18ce4afeb94e6d2",
            "POINT_DERIVATIVE_BASIN_BRACKETED",
            "MINIMUM_ORIENTED",
            "SCHUR_OUT_OF_H1_SCOPE",
            "applicable_primary_count=0",
            "dP/dL=-envelopeNormSq/L+remainder_drift_L",
            "L*remainder_drift_L/envelopeNormSq",
            "PR #117 remains the Control-v2 semantic anchor",
            "PR #207",
            "7e186ede13beece95e8a08b2449cd3accbe5b2f5",
            "oddBad_or_sourceMomentMomentFour_re_pos_of_even",
            "PR #209",
            "a6f0e5d3db988eeaf3ed54cf283f85b8d23f5392",
            "oddBad_or_sourceMomentMixedJet_re_neg_of_even",
            "evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad",
            "even-selected odd-good branch is PROVED through #209",
            "OBS-059Q is CLOSED / PROVED BY #209",
            "PR #211",
            "704a69e41871269814ba091e9476fe76b2d09844",
            "explicitCanonicalSourceMoment_eq_completeSourceFunctional",
            "oddBad_or_completeSourceFunctionalMixedJet_re_neg_of_even",
            "OBS-059I remains OPEN / ACTIVE",
            "SOURCE_COORDINATE_KERNEL_FOR_COMPLETE_FUNCTIONAL",
            "simultaneous odd-bad branch",
            "RH remains OPEN",
        ):
            self.assertIn(token, note)
        self.assertEqual(control["merged_theorem_anchor"]["pr"], 211)
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

    def test_regular_schur_action_is_post184_remainder_incompatibility_route(self):
        registry = json.loads(
            (RHRC / "control_v2" / "ACTION_REGISTRY.json").read_text(encoding="utf-8")
        )
        action = registry["actions"]["E4_A4_REGULAR_SCHUR_ENERGY_SIGN"]
        objections = "\n".join(action["surviving_objections"])
        first_breaks = "\n".join(x["statement"] for x in action["first_breaks"])
        break_ids = [x["id"] for x in action["first_breaks"]]

        for token in (
            "PR #163",
            "PR #180",
            "PR #182",
            "PR #184",
            "complex-Hermitian",
            "M~(t)=-tI+R~(t)",
            "P_t'=-envelopeNormSq+remainderEnvelopeDerivative",
            "q13->16/N2/K3/even",
            "FIXED_UNIT_METHOD_ACCEPTED",
            "DERIVATIVE_UNRESOLVED",
            "POINT_DERIVATIVE_BASIN_BRACKETED",
            "MINIMUM_ORIENTED",
            "SCHUR_OUT_OF_H1_SCOPE",
            "applicable_primary_count=0",
            "dP/dL=-envelopeNormSq/L+remainder_drift_L",
            "L*remainder_drift_L/envelopeNormSq",
            "canonical intrinsic cubic shell",
            "global aperture and global minimizing-Schur monotonicity remain quarantined",
            "DR-024",
        ):
            self.assertIn(token, objections)

        self.assertEqual(action["dead_route_matches"], [])
        self.assertEqual(break_ids, ["E4A4-SCHUR-FB-05"])
        self.assertIn("#165-#184", first_breaks)
        self.assertIn("source-specific", first_breaks)
        self.assertIn("same state", first_breaks)
        self.assertIn("without restating successor positivity", first_breaks)

        selected_break = _selected_first_break(
            registry, "E4_A4_REGULAR_SCHUR_ENERGY_SIGN"
        )
        self.assertIsNotNone(selected_break)
        self.assertEqual(selected_break["break_id"], "E4A4-SCHUR-FB-05")

    def test_fb05_incompatibility_program_is_same_state_and_claim_capped(self):
        program = (RHRC / "FB05_INCOMPATIBILITY_PROGRAM.md").read_text(encoding="utf-8")
        for token in (
            "same state",
            "same aperture",
            "same parity",
            "same normalization",
            "ArithmeticSideSubexponential",
            "negative-index",
            "67.25%",
            "Do not count them as two independent",
            "Sparse-exception test",
            "Mustache test",
            "PR #184",
            "PR #207",
            "complex-Hermitian",
            "remainder domination",
            "coordinate",
            "FB-05",
            "RH remains OPEN",
        ):
            self.assertIn(token, program)

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