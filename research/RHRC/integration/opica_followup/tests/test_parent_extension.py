"""Adversarial structural extension checks; fixtures are not proof receipts."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('followup_extension', HERE / 'parent_extension.py')
extension = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = extension
spec.loader.exec_module(extension)


class ParentExtensionTests(unittest.TestCase):
    def setUp(self):
        self.parent = json.loads((HERE / 'PROTECTED_STATE.json').read_text(encoding='utf-8'))
        descriptor_bytes = (HERE / 'PARENT_EXTENSION.json').read_bytes()
        descriptor = json.loads(descriptor_bytes)
        self.descriptor = descriptor
        # Synthetic complete child objects demonstrate projection mechanics.
        # They are never registered and cannot satisfy compiler/type gates.
        roots_bytes = (HERE / 'PUBLIC_ROOTS.json').read_bytes()
        roots = {root['id']: root for root in json.loads(roots_bytes)['roots']}
        claims = [{'id': identity, 'theorem': roots[identity]['full_name'],
                   'source': roots[identity]['path'], 'status': 'FIXTURE_ONLY'}
                  for identity in descriptor['child_claim_ids']]
        bindings = [{key: claim[key] for key in ('id', 'theorem', 'source')} for claim in claims]
        self.contract = {'descriptor_bytes': descriptor_bytes, 'roots_bytes': roots_bytes,
                         'reviewed_claim_objects': claims, 'reviewed_binding_objects': bindings}
        self.raw = deepcopy(self.parent)
        self.raw['claim_registry']['claims'] += deepcopy(claims)
        self.raw['theorem_bindings']['bindings'] += deepcopy(bindings)
        rules = self.raw['file_classes']['rules']
        index = next(i for i, rule in enumerate(rules) if rule['id'] == 'zeta_lean')
        rules[index:index] = deepcopy(descriptor['child_classes'])
        self.raw['semantic_closure']['standalone_module_roles'].update(descriptor['child_roles'])
        self.raw['files'] += [{'path': path, 'mode': '100644', 'git_blob': '0' * 40,
                               'bytes': 0, 'sha256': '0' * 64}
                              for path in descriptor['new_exact_paths']]

    def check(self):
        return extension.validate_extension_context(self.raw, self.parent, self.contract)

    def reject(self):
        with self.assertRaises(extension.ExtensionError):
            self.check()

    def test_exact_projection_preserves_every_parent_value(self):
        result = self.check()
        expected = {key: self.parent[key] for key in
                    ('claim_registry', 'theorem_bindings', 'file_classes', 'semantic_closure')}
        self.assertEqual(dict(extension.project_parent_context(result)), expected)
        self.assertEqual(extension.allowed_child_delta(result),
                         frozenset(self.descriptor['new_exact_paths'] +
                                   self.descriptor['modified_exact_paths'] +
                                   self.descriptor['generated_exact_paths']))
        self.raw['claim_registry']['claims'][0]['status'] = 'CORRUPTED_AFTER_VALIDATION'
        self.assertEqual(dict(extension.project_parent_context(result)), expected)

    def test_raw_state_cannot_be_projected(self):
        with self.assertRaises(extension.ExtensionError):
            extension.project_parent_context(self.raw)

    def test_old_claim_mutation(self):
        self.raw['claim_registry']['claims'][0]['statement'] = 'False'
        self.reject()

    def test_old_claim_deletion(self):
        del self.raw['claim_registry']['claims'][0]
        self.reject()

    def test_duplicate_claim_identity(self):
        self.raw['claim_registry']['claims'].append(deepcopy(self.raw['claim_registry']['claims'][0]))
        self.reject()

    def test_unlisted_child_claim(self):
        self.raw['claim_registry']['claims'].append({'id': 'OPICA_FOLLOWUP_EXTRA'})
        self.reject()

    def test_child_statement_mutation(self):
        self.raw['claim_registry']['claims'][-1]['status'] = 'PROVED_UNCONDITIONAL'
        self.reject()

    def test_old_binding_mutation(self):
        self.raw['theorem_bindings']['bindings'][0]['theorem'] = 'False.elim'
        self.reject()

    def test_child_binding_wrong_theorem(self):
        self.raw['theorem_bindings']['bindings'][-1]['theorem'] = 'False.elim'
        self.reject()

    def test_coordinated_theorem_substitution(self):
        self.raw['theorem_bindings']['bindings'][-1]['theorem'] = 'False.elim'
        self.raw['claim_registry']['claims'][-1]['theorem'] = 'False.elim'
        self.contract['reviewed_binding_objects'][-1]['theorem'] = 'False.elim'
        self.contract['reviewed_claim_objects'][-1]['theorem'] = 'False.elim'
        self.reject()

    def test_missing_root_inventory(self):
        del self.contract['roots_bytes']
        self.reject()

    def test_changed_parent_registry_metadata(self):
        self.raw['claim_registry']['schema_version'] = 'weakened'
        self.reject()

    def test_candidate_binding_mutation(self):
        self.raw['theorem_bindings']['candidate_scope'] = 'weakened'
        self.reject()

    def test_missing_descriptor(self):
        del self.contract['descriptor_bytes']
        self.reject()

    def test_descriptor_allowlist_expansion(self):
        self.descriptor['new_exact_paths'].append('Zeta23/Arbitrary.lean')
        self.contract['descriptor_bytes'] = json.dumps(self.descriptor).encode()
        self.reject()

    def test_wrong_parent(self):
        self.raw['parent_head'] = '0' * 40
        self.reject()

    def test_wrong_tree(self):
        self.parent['parent_tree'] = '0' * 40
        self.reject()

    def test_protected_source_drift(self):
        row = next(r for r in self.raw['files'] if r['path'].startswith('Zeta23/OPICA/'))
        row['sha256'] = '1' * 64
        self.reject()

    def test_missing_parent_source(self):
        del self.raw['files'][0]
        self.reject()

    def test_unlisted_source(self):
        self.raw['files'].append({'path': 'Zeta23/OPICAFollowup/Extra.lean',
                                  'mode': '100644', 'sha256': '0' * 64})
        self.reject()

    def test_missing_full_scope_file(self):
        self.raw['files'].pop()
        self.reject()

    def test_path_traversal(self):
        self.raw['files'][-1]['path'] = '../escape.lean'
        self.reject()

    def test_symlink_mode(self):
        self.raw['files'][-1]['mode'] = '120000'
        self.reject()

    def test_shadowing_parent_classification(self):
        self.raw['file_classes']['rules'].insert(0, {'id': 'bypass', 'pattern': '.*',
                                                   'trust_zone': 'AUDIT_ONLY'})
        self.reject()

    def test_old_role_changed(self):
        roles = self.raw['semantic_closure']['standalone_module_roles']
        key = next(k for k in roles if not k.startswith('Zeta23.OPICAFollowup'))
        roles[key] = 'AUDIT_ONLY'
        self.reject()

    def test_only_generated_and_authorized_edits_may_change(self):
        allowed = set(self.descriptor['modified_exact_paths'] + self.descriptor['generated_exact_paths'])
        for row in self.raw['files']:
            if row['path'] in allowed:
                row['sha256'] = 'f' * 64
        self.check()


if __name__ == '__main__':
    unittest.main()
