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
        self.assertEqual(state.anchor.pr, 271)
        self.assertEqual(
            state.anchor.merge_commit,
            "c9fb1a6462e5cc828acb951aefd4e9fae33ddaaa",
        )
        self.assertEqual(
            state.anchor.tree,
            "10ba766b13e63fb5e5567c3da7a3910f54fe6812",
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

    def test_control_note_preserves_history_and_records_current_theorem_state(self):
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
            "PR #213",
            "703c3764a7d35aa4801e791a1929efa54c2533a1",
            "explicitCanonicalSourceMoment_eq_sourceKernelRHS",
            "oddBad_or_sourceKernelMixedJet_re_neg_of_even",
            "EXACT_KERNEL_ADVERSARIAL_FALSIFICATION",
            "sourceAtomRealEnergy",
            "quadraticNormalSourceAtom",
            "simultaneous odd-bad branch",
            "PR #224",
            "83de9193dffba12097d950d2291348db76d047f7",
            "0f8f5ad468b337622942f76725c9d76db74e27e4",
            "cubicProjectionResidual_eq_oddCubicProjectionSlope_smul",
            "predecessor-correction proportionality is the next theorem target",
            "PR #226",
            "8279384b0dfe44f3853bb8532789107ec59d0f82",
            "oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul",
            "PR #227",
            "b8d29733167a95e16f5721eddfced6b650a3b641",
            "7aace87a5644f837e2c8b64bdcf5e66b2dc0b020",
            "crossParitySecularGamma_eq_one_add_kappa_mul_one_sub_alpha",
            "BiRegularCellMinimalNegativeEnergyCertificate.exists_evenOddZeroShiftOneCoefficientNormalForm_of_even",
            "CROSS_PARITY_CORRECTION_FUNCTIONAL_RIESZ_REPRESENTATION",
            "Alpha reality/sign is NOT proved",
            "PR #229",
            "9d4f81c171264be424fbac40f1211263c3cc6abd",
            "992398c810de5fb84919846fc4192d709d51e783",
            "oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div",
            "one_sub_crossParitySecularAlpha_eq_resolvent_pairing_div",
            "one_sub_crossParitySecularGamma_eq_resolvent_pairing_div",
            "13/13 GREEN JOBS",
            "CROSS_PARITY_CORRECTION_SOURCE_COUPLING",
            "CANONICAL_SOURCE_COUPLING_AND_RETAINED_SOURCE_BALANCE",
            "Alpha reality/sign remains OPEN after #229",
            "PR #231",
            "f9623be705955bd98ef563aa75d3244712009cac",
            "0d0305da1390206a4531ac2cbca52e45b19f2cad",
            "5d50bd188db58e76b47e768bcad0e815356fb9dd",
            "star_oddSafeSecularCorrectionFunctional_mul_shellInner_eq_cubicShellCoupling",
            "evenShiftedCrossParitySourceBalance_of_even_of_not_oddBad",
            "RETAINED_CROSS_PARITY_SOURCE_GRAM_DISK",
            "GOOD_SECTOR_GRAM_CONTROL_COMPOSED_WITH_RETAINED_SOURCE_BALANCE",
            "PR #233",
            "565428e066004e559490fbe1d21d46ef14494de3",
            "9dfee4f50d5b57c92327da564ddf2f6159223fe1",
            "5713b8d8088864cb126aae48a3a5a5ac8304807a",
            "RETAINED_SOURCE_DISK_SECULAR_INTERSECTION",
            "M4_FREE_RETAINED_DISK_HALFPLANE_COMPATIBILITY",
            "PR #234",
            "6d9b60752f7a4f164113bb0602fcdee87e2a54a1",
            "b18d81f11a04982e438b7e196853ae665dab0cc2",
            "94a0db085c35d2aba753a8359e452e4189c5c897",
            "RETAINED_SOURCE_KERNEL_FORBIDDEN_QUADRANT",
            "CANONICAL_SOURCE_DEFICIT_AND_EXCESS_SIGN_CONTROL",
            "CANONICAL_CUBIC_SHELL_NORMALIZATION",
            "PR #235",
            "d7ae288e874b2cf3462a8e00c35c7b713607a192",
            "a66e1c617033f4adaa52e935668399efb93048ac",
            "5ef597b1d75075ec2299261a4193432a36932ffe",
            "RETAINED_SOURCE_KERNEL_FORBIDDEN_QUADRANT",
            "RETAINED_CANONICAL_REAL_PHASE_COLLAPSE",
            "CONJUGATION_COMPATIBLE_CANONICAL_NORMALIZATION",
            "PR #236",
            "45491342f5661429679579c7889c1ad8b96728b6",
            "a66e1c617033f4adaa52e935668399efb93048ac",
            "5ef597b1d75075ec2299261a4193432a36932ffe",
            "RETAINED_CANONICAL_REAL_PHASE_COLLAPSE",
            "RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR",
            "REALITY_OF_RETAINED_M4_AND_SCALAR_COMPOSITION",
            "PR #236",
            "45491342f5661429679579c7889c1ad8b96728b6",
            "a66e1c617033f4adaa52e935668399efb93048ac",
            "5ef597b1d75075ec2299261a4193432a36932ffe",
            "RETAINED_CANONICAL_REAL_PHASE_COLLAPSE",
            "RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR",
            "REALITY_OF_RETAINED_M4_AND_SCALAR_COMPOSITION",
            "PR #237",
            "8b7ba6b25c6f8977ff27890196e5b43ca3459b78",
            "267d417216f1731c6860b7553ba87397843fe258",
            "28b22a2a4c96f32874fc09cd1e73f2fb09807e9d",
            "RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR",
            "CANONICAL_REAL_NEGATIVE_SHIFT_TRANSFER_GEOMETRY",
            "CONJUGATION_COMPATIBLE_SHIFTED_RESOLVENT_AND_REAL_TRANSFER_COEFFICIENTS",
            "retained Gamma reality",
            "RH remains OPEN",
            "PR #242",
            "NoRegularFirstBadCertificates -> Mathlib.RiemannHypothesis",
            "OFFLINE_GENERATED_WHOLE_CELL_RETAINED_FAMILY",
            "PR #243",
            "arbitrarily large retained aperture",
            "GENERATED_FAMILY_FINAL_GATE",
            "Post-#271 current override",
            "PR #271 is merged-green theorem authority",
            "legal parity-ground simplicity iff strict parity separation",
            "carrier-wide source-weight monotonicity counterexample",
            "CofinalCanonicalArithmeticCertificates",
            "PR #270 is framework/graph authority only",
        ):
            self.assertIn(token, note)
        self.assertEqual(control["merged_theorem_anchor"]["pr"], 271)
        self.assertEqual(control["latest_validated_theorem_delta"]["pr"], 271)
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