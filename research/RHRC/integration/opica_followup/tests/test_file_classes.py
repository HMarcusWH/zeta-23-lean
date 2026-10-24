"""First-match, role and audit-boundary tests using production classification code."""
from copy import deepcopy
import importlib.util
import json
import os
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
REPO = Path(os.environ.get('OPICA_TEST_REPO', HERE.parents[3])).resolve()
sys.path.insert(0, str(REPO / 'research/RHRC/graph'))
spec = importlib.util.spec_from_file_location('runtime_actual_graph_classifier', REPO / 'research/RHRC/graph/build.py')
graph = importlib.util.module_from_spec(spec); spec.loader.exec_module(graph)


class FollowupFileClassTests(unittest.TestCase):
    def setUp(self):
        source = REPO / 'research/RHRC/integration/opica_followup/tests/test_parent_extension.py'
        spec = importlib.util.spec_from_file_location('fileclass_existing_extension_fixture', source)
        self.module = importlib.util.module_from_spec(spec); spec.loader.exec_module(self.module)
        self.fixture = self.module.ParentExtensionTests('test_exact_projection_preserves_every_parent_value')
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.manifest = json.loads((REPO / 'research/RHRC/integration/opica_followup/BUILD_MANIFEST.json').read_text())

    def check(self): return self.fixture.check()
    def reject(self):
        with self.assertRaises(self.module.extension.ExtensionError): self.check()

    def test_every_historical_first_match_and_role_is_preserved(self):
        old = self.fixture.parent['file_classes']; new = self.fixture.raw['file_classes']
        for row in self.fixture.parent['files']:
            with self.subTest(path=row['path']):
                self.assertEqual(graph.classify(row['path'], old), graph.classify(row['path'], new))
        old_roles = self.fixture.parent['semantic_closure']['standalone_module_roles']
        new_roles = self.fixture.raw['semantic_closure']['standalone_module_roles']
        self.assertTrue(all(new_roles[name] == role for name, role in old_roles.items()))
        self.check()

    def test_exact_child_math_and_audit_zones_match_frozen_contract(self):
        config = self.fixture.raw['file_classes']
        for module in self.manifest['modules']:
            with self.subTest(module=module['module']):
                actual = graph.classify(module['path'], config)
                self.assertEqual(actual[:2], ('LEAN_SOURCE', module['trust_zone']))
        self.check()

    def test_native_child_cannot_be_promoted_to_formal_core_by_a_new_rule(self):
        self.fixture.raw['file_classes']['rules'].insert(0, {'id': 'unauthorized_native_promotion',
            'pattern': '^Zeta23/OPICAFollowup/Native', 'file_class': 'LEAN_SOURCE', 'trust_zone': 'RH_FORMAL_CORE'})
        self.reject()

    def test_parent_first_match_shadowing_is_rejected(self):
        self.fixture.raw['file_classes']['rules'].insert(0, {'id': 'shadow_everything',
            'pattern': '.*', 'file_class': 'DOCUMENTATION', 'trust_zone': 'AUDIT_ONLY'})
        self.reject()

    def test_reordering_old_rules_cannot_change_first_match_meaning(self):
        rules = self.fixture.raw['file_classes']['rules']
        rules[0], rules[-1] = rules[-1], rules[0]
        self.reject()

    def test_unknown_path_stays_unknown_without_a_matching_rule(self):
        result = graph.classify('unclassified-extension-without-suffix', self.fixture.parent['file_classes'])
        self.assertEqual(result, ('UNKNOWN_FILE_CLASS', 'UNKNOWN', 'no_matching_rule'))

    def test_parent_semantic_role_cannot_be_overwritten(self):
        name = next(iter(self.fixture.parent['semantic_closure']['standalone_module_roles']))
        self.fixture.raw['semantic_closure']['standalone_module_roles'][name] = 'OPICA_AUDIT_ONLY'
        self.reject()

    def test_extra_child_role_is_rejected_even_if_its_name_looks_legitimate(self):
        self.fixture.raw['semantic_closure']['standalone_module_roles']['Zeta23.OPICAFollowup.Unlisted'] = 'OPICA_GENERIC_FORMALIZATION'
        self.reject()

    def test_unlisted_extra_path_is_rejected_despite_matching_child_class(self):
        self.fixture.raw['files'].append({'path': 'Zeta23/OPICAFollowup/Unlisted.lean',
            'mode': '100644', 'git_blob': '0' * 40, 'bytes': 0, 'sha256': '0' * 64})
        self.reject()

    def test_current_public_facade_reaches_only_mathematical_modules(self):
        # Actual source header graph, not lexical proof or accepted implementation review.
        path = REPO / 'research/RHRC/integration/opica_followup/build_receipt.py'
        spec = importlib.util.spec_from_file_location('fileclass_actual_child_receipt', path)
        builder = importlib.util.module_from_spec(spec); spec.loader.exec_module(builder)
        contract = builder.full_contract(REPO)
        edges = builder.full_import_graph(REPO, contract)
        self.assertEqual(set(edges), set(contract['mathematical_modules']))
        self.assertNotIn(builder.VALIDATION_MODULE, set().union(*(set(v) for v in edges.values())))

    def test_audit_import_in_math_source_is_rejected_by_production_graph_gate(self):
        path = REPO / 'research/RHRC/integration/opica_followup/tests/test_receipt.py'
        spec = importlib.util.spec_from_file_location('fileclass_existing_full_receipt_fixture', path)
        module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        fixture = module.FullReceiptTests('test_complete_synthetic_structure_has_no_release_authority')
        self.addCleanup(fixture.doCleanups); fixture.setUp()
        source = fixture.repo / 'Zeta23/OPICAFollowup/NativeFilters.lean'
        source.write_text('import Zeta23.OPICAFollowup.Validation\n' + source.read_text(), encoding='utf-8')
        with self.assertRaisesRegex(ValueError, 'audit-only import'):
            module.receipt.full_import_graph(fixture.repo, fixture.contract)


if __name__ == '__main__': unittest.main()
