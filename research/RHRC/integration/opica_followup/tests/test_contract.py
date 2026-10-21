"""Supplemental inputs cannot silently replace or expand frozen acceptance."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('followup_contract', HERE / 'validate_contract.py')
contract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contract)


class FrozenAcceptanceTests(unittest.TestCase):
    def setUp(self):
        read = lambda name: json.loads((HERE / name).read_text(encoding='utf-8'))
        self.manifest, self.public, self.crosswalk, self.extension, self.register = map(read,
            ('BUILD_MANIFEST.json', 'PUBLIC_ROOTS.json', 'PAPER_CROSSWALK.json',
             'PARENT_EXTENSION.json', 'SOURCE_REGISTER.json'))
        repo = HERE.parents[3]
        self.helper_source = (repo / 'Zeta23/OPICAFollowup/NormFirstTransfer.lean').read_text(encoding='utf-8')
        self.validation_source = (repo / 'Zeta23/OPICAFollowup/Validation.lean').read_text(encoding='utf-8')

    def test_original_inventory_and_supplement_pass(self):
        self.assertEqual(contract.metadata_errors(self.manifest, self.public,
                                                  self.crosswalk, self.extension), [])
        self.assertEqual(contract.supplemental_errors(self.register), [])
        self.assertEqual(len(self.public['roots']), 100)
        self.assertEqual(len(self.crosswalk['scope_units']), 28)

    def test_versioned_dependency_refinement_passes(self):
        self.assertEqual(contract.dependency_amendment_errors(self.register, self.manifest), [])

    def test_dependency_refinement_cannot_drop_primary_scope(self):
        self.register['implementation_dependency_amendment']['primary_roots'] = 99
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_change_statements(self):
        self.register['implementation_dependency_amendment']['rows'][0]['theorem_statement_changes'] = ['weaken']
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_add_assumptions(self):
        self.register['implementation_dependency_amendment']['rows'][0]['new_assumptions'] = ['RH']
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_authorize_arbitrary_import(self):
        self.register['implementation_dependency_amendment']['rows'][0]['approved_direct_project_imports'].append('Zeta23.Fake')
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_rewrite_frozen_plan(self):
        self.register['implementation_dependency_amendment']['rows'][0]['planned_direct_project_imports'] = []
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_promote_optional_lemma(self):
        self.register['implementation_dependency_amendment']['promoted_supporting_lemmas'] = ['C1']
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_requires_exact_rows(self):
        self.register['implementation_dependency_amendment']['rows'].pop()
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_erase_previous_version(self):
        self.register['implementation_dependency_history'] = []
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_rewrite_previous_version(self):
        self.register['implementation_dependency_history'][0]['new_assumptions'] = ['RH']
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_cannot_rewrite_second_version(self):
        self.register['implementation_dependency_history'][1]['primary_roots'] = 37
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_dependency_refinement_history_order_is_bound(self):
        self.register['implementation_dependency_history'].reverse()
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest))

    def test_drop_hard_original_root(self):
        self.public['roots'] = [r for r in self.public['roots'] if r['full_name'] !=
                               'Zeta23.OPICAFollowup.native_slow_source_window_rate']
        self.assertTrue(contract.metadata_errors(self.manifest, self.public,
                                                 self.crosswalk, self.extension))

    def test_duplicate_original_root(self):
        self.public['roots'][-1] = deepcopy(self.public['roots'][0])
        self.assertTrue(contract.metadata_errors(self.manifest, self.public,
                                                 self.crosswalk, self.extension))

    def test_missing_original_acceptance_unit(self):
        self.crosswalk['scope_units'].pop()
        self.assertTrue(contract.metadata_errors(self.manifest, self.public,
                                                 self.crosswalk, self.extension))

    def test_amendment_text_tampering(self):
        self.register['supplemental_research_inputs'][0]['utf8'] += '\nRH proved\n'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_optional_candidate_cannot_become_mandatory(self):
        self.register['supplemental_crosswalk'][0]['required'] = True
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_amendment_cannot_add_primary_root(self):
        self.register['supplemental_research_inputs'][0]['new_mandatory_roots'] = ['SHARP_TRANSFER']
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_amendment_cannot_add_unlisted_module(self):
        self.register['supplemental_research_inputs'][0]['new_paths'] = ['Zeta23/Extra.lean']
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_amendment_cannot_close_independent_upper(self):
        self.register['supplemental_crosswalk'][2]['independent_closing_inequalities'] = 'PROVED'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_unformalized_polynomial_measure_theorem_cannot_be_promoted(self):
        self.register['supplemental_crosswalk'][1]['status'] = 'PROVED'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c3_counterexample_cannot_be_erased(self):
        self.register['supplemental_crosswalk'][2]['status'] = 'PROVED'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_optional_candidate_cannot_close_step4(self):
        self.register['supplemental_crosswalk'][0]['Step4'] = 'PROVED'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_top_level_rh_cannot_be_promoted(self):
        self.register['RH'] = 'PROVED'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_top_level_step4_cannot_be_promoted(self):
        self.register['Step4'] = 'PROVED'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c1_proof_status_cannot_be_arbitrarily_promoted(self):
        self.register['supplemental_crosswalk'][0]['status'] = 'PROVED_WITHOUT_RECEIPT'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c1_missing_helper_rejected(self):
        self.register['supplemental_crosswalk'][0]['supporting_declarations'].pop()
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c1_nonexistent_helper_rejected(self):
        self.register['supplemental_crosswalk'][0]['supporting_declarations'][0] = 'NoSuchTheorem'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c1_duplicate_helper_rejected(self):
        helpers = self.register['supplemental_crosswalk'][0]['supporting_declarations']
        helpers[-1] = helpers[0]
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c1_defining_source_cannot_change(self):
        self.register['supplemental_crosswalk'][0]['home'] = 'Zeta23/Extra.lean'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c1_expected_type_check_claim_cannot_disappear(self):
        self.register['supplemental_crosswalk'][0]['expected_type_checks'] = 'none'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_exact_c1_source_and_consumers_pass_inventory(self):
        self.assertEqual(contract.candidate1_source_errors(self.helper_source, self.validation_source), [])

    def test_c1_helper_replaced_by_axiom_fails_inventory(self):
        mutated = self.helper_source.replace('lemma sharpNormAlpha_pos', 'axiom sharpNormAlpha_pos', 1)
        self.assertTrue(contract.candidate1_source_errors(mutated, self.validation_source))

    def test_c1_renamed_expected_consumer_fails_inventory(self):
        mutated = self.validation_source.replace('theorem expected_sharp_norm_first_arsinh_bound',
            'theorem expected_unchecked_sharp_bound', 1)
        self.assertTrue(contract.candidate1_source_errors(self.helper_source, mutated))

    def test_c1_consumer_name_in_comment_is_not_a_declaration(self):
        mutated = self.validation_source.replace('theorem expected_sharp_norm_first_arsinh_bound',
            '/- theorem expected_sharp_norm_first_arsinh_bound -/', 1)
        self.assertTrue(contract.candidate1_source_errors(self.helper_source, mutated))

    def test_c1_duplicate_consumer_fails_inventory(self):
        mutated = self.validation_source + '\ntheorem expected_sharp_norm_first_arsinh_bound : True := by trivial\n'
        self.assertTrue(contract.candidate1_source_errors(self.helper_source, mutated))

    def test_c1_nested_comments_and_strings_do_not_add_helpers(self):
        extra = ('\n/- outer\n/- nested -/\nlemma sharp_fake : True := by trivial\n-/\n'
                 'def fixtureString := "lemma sharp_fake : True := by trivial"\n')
        self.assertEqual(contract.candidate1_source_errors(self.helper_source + extra,
                                                         self.validation_source), [])

    def test_comment_splitting_cannot_manufacture_declaration_keyword(self):
        names = contract.lean_declaration_names('the/- comment -/orem expected_sharp_fake : True := by trivial\n')
        self.assertEqual(names, [])

    def test_c3_missing_embedded_counterexample_pointer_rejected(self):
        candidate = next(row for row in self.register['amendment_v1_1_evaluation']['candidates']
                         if row['id'] == 'C3')
        candidate.pop('counterexample_json_pointer')
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c3_wrong_embedded_counterexample_pointer_rejected(self):
        candidate = next(row for row in self.register['amendment_v1_1_evaluation']['candidates']
                         if row['id'] == 'C3')
        candidate['counterexample_json_pointer'] = '/supplemental_crosswalk/0/falsification'
        self.assertTrue(contract.supplemental_errors(self.register))

    def test_c3_embedded_counterexample_target_cannot_disappear(self):
        self.register['supplemental_crosswalk'][2].pop('falsification')
        self.assertTrue(contract.supplemental_errors(self.register))


if __name__ == '__main__':
    unittest.main()
