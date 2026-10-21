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

    def test_original_inventory_and_supplement_pass(self):
        self.assertEqual(contract.metadata_errors(self.manifest, self.public,
                                                  self.crosswalk, self.extension), [])
        self.assertEqual(contract.supplemental_errors(self.register), [])
        self.assertEqual(len(self.public['roots']), 100)
        self.assertEqual(len(self.crosswalk['scope_units']), 28)

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


if __name__ == '__main__':
    unittest.main()
