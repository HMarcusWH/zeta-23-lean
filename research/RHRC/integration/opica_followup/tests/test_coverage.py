"""Attack full-scope type/source/domain bindings using actual production validators.

The existing synthetic receipt fixture tests protocol rejection only. Neither
its test-only seal nor these source mutations establish mathematical semantics.
Actual Lean and independent semantic review remain separate mandatory gates.
"""
from copy import deepcopy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
REPO = Path(os.environ.get('OPICA_TEST_REPO', HERE.parents[3])).resolve()


class FullClauseCoverageTests(unittest.TestCase):
    def setUp(self):
        source = REPO / 'research/RHRC/integration/opica_followup/tests/test_receipt.py'
        spec = importlib.util.spec_from_file_location('coverage_existing_receipt_fixture', source)
        module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        self.fixture = module.FullReceiptTests('test_complete_synthetic_structure_has_no_release_authority')
        self.addCleanup(self.fixture.doCleanups)
        self.fixture.setUp()
        self.builder = module.receipt

    def reseal_fixture_only(self):
        self.fixture.write_review()
        self.builder.FULL_REVIEW_SHA256 = self.builder.object_sha256(self.fixture.review)

    def validate_review(self):
        return self.builder.reviewed_full_contract(self.fixture.repo, self.fixture.contract)

    def test_99_roots_cannot_cover_the_original100_even_in_a_resealed_fixture(self):
        self.fixture.review['roots'].pop(); self.reseal_fixture_only()
        with self.assertRaises(ValueError): self.validate_review()

    def test_missing_original_acceptance_unit_cannot_be_hidden_by100_names(self):
        self.fixture.review['units'].pop(); self.reseal_fixture_only()
        with self.assertRaises(ValueError): self.validate_review()

    def test_absent_frozen_subclause_binding_is_rejected(self):
        self.fixture.review['roots'][0]['frozen_contract_sha256'] = '0' * 64
        self.reseal_fixture_only()
        with self.assertRaises(ValueError): self.validate_review()

    def test_frozen_source_and_domain_contract_cannot_be_rewritten(self):
        path = self.fixture.folder / 'PUBLIC_ROOTS.json'
        data = json.loads(path.read_text())
        data['roots'][0]['statement_contract'] = 'Only a toy source subcase is required.'
        path.write_text(json.dumps(data), encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'frozen full scope changed'):
            self.builder.full_contract(self.fixture.repo)

    def test_one_copy_source_replacements_invalidate_the_sealed_source_binding(self):
        path = self.fixture.repo / self.fixture.contract['roots'][0]['path']
        original = path.read_bytes()
        for replacement in [b'-- substituted q*j\n', b'-- substituted Pj\n', b'-- synthetic native source\n']:
            with self.subTest(replacement=replacement):
                path.write_bytes(original + replacement)
                with self.assertRaises(ValueError): self.validate_review()
        # No parser here is being represented as a mathematical source checker.

    def test_caller_source_property_cannot_be_added_to_the_original_typed_root(self):
        row = self.fixture.data['declarations'][0]
        row['type_expression'] = {'format': 'LEAN_EXPR_DAG_V1', 'root': '1', 'nodes': [
            ['sort', ['zero']], ['forall', ['str', ['anonymous'], 'assumed_native_rate'], 'default', '0', '0']]}
        encoded = json.dumps(row['type_expression'], ensure_ascii=False, separators=(',', ':'))
        row['type_sha256'] = hashlib.sha256(encoded.encode()).hexdigest()
        row['type_metrics'] = self.builder.validate_expression(encoded)
        with self.assertRaisesRegex(ValueError, 'reviewed expected type changed'):
            self.builder.validate_compiler_records(self.fixture.data, self.fixture.reviewed['queries'],
                mathematical_modules=self.fixture.contract['export_modules'])

    def test_optional_bridge_cannot_replace_the_original_expected_consumer(self):
        self.fixture.review['roots'][0]['expected_type_consumer'] = self.builder.VALIDATION_MODULE + '.optional_bridge'
        self.reseal_fixture_only()
        with self.assertRaises(ValueError): self.validate_review()

    def test_root_use_alone_cannot_replace_an_explicit_physical_consumer(self):
        self.fixture.review['roots'][0]['physical_or_domain_consumers'] = []
        self.reseal_fixture_only()
        with self.assertRaises(ValueError): self.validate_review()

    def test_asserted_coverage_outside_actual_validation_module_is_rejected(self):
        self.fixture.review['consumers'][0]['module'] = 'Zeta23.OPICAFollowup.NativeFilters'
        self.reseal_fixture_only()
        with self.assertRaises(ValueError): self.validate_review()

    def test_self_reported100_coverage_cannot_create_independent_review(self):
        with patch.object(self.builder, 'FULL_REVIEW_SHA256', None):
            with self.assertRaisesRegex(ValueError, 'review seal'):
                self.validate_review()


if __name__ == '__main__': unittest.main()
