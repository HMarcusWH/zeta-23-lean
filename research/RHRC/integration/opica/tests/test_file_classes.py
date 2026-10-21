from __future__ import annotations
import json
import copy
import importlib.util
from pathlib import Path
import re
import unittest

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[3]
spec = importlib.util.spec_from_file_location('opica_class_contract',HERE/'validate_contract.py')
contract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contract)


class FileClasses(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.classes = json.loads((REPO/'research/RHRC/graph/FILE_CLASSES.json').read_text(encoding='utf-8'))
        cls.rules = cls.classes['rules']
        cls.closure = json.loads((REPO/'research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json').read_text(encoding='utf-8'))
        cls.manifest = json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))
        cls.register = json.loads((HERE/'SOURCE_REGISTER.json').read_text(encoding='utf-8'))
        cls.old_classes,cls.old_closure,cls.old_paths = contract.baseline_configs(REPO,cls.manifest['base_commit'])

    def config_errors(self,classes=None,closure=None):
        return contract.config_errors(classes if classes is not None else self.classes,
            closure if closure is not None else self.closure,self.old_classes,self.old_closure,
            self.manifest['modules'],self.old_paths)

    def classify(self, path):
        return next((r for r in self.rules if re.search(r['pattern'], path)), None)

    def test_every_new_path_is_classified(self):
        for entry in self.manifest['create']:
            with self.subTest(path=entry['path']):
                self.assertIsNotNone(self.classify(entry['path']))

    def test_all_mathematical_and_audit_modules_have_exact_trust(self):
        self.assertEqual(contract.classification_errors(self.classes,self.manifest['modules'],self.register),[])
        native_paths = {'Zeta23/OPICA/NativeJetAdapter.lean','Zeta23/OPICA/NativeArithmeticAdapter.lean'}
        for entry in self.manifest['modules']:
            with self.subTest(module=entry['module']):
                rule = self.classify(entry['path'])
                self.assertEqual(rule['file_class'], 'LEAN_SOURCE')
                if entry['path'] in native_paths:
                    self.assertEqual(entry['trust_zone'],'RH_FORMAL_CORE')
                    self.assertEqual(rule['trust_zone'],'AUXILIARY_FORMALIZATION')
                    self.assertEqual(self.closure['standalone_module_roles'][entry['module']],
                        'OPICA_SOURCE_BOUND_NATIVE_ADAPTER')
                else:
                    self.assertEqual(rule['trust_zone'], entry['trust_zone'])

    def test_native_file_refinement_cannot_be_undocumented_or_broadened(self):
        original = self.register['implementation_file_classification_overrides']
        for overrides in [None,[],original[:1],original+[original[0]],
            [dict(original[0],path='Zeta23/OPICA/WeightedLaplace.lean'),original[1]],
            [dict(original[0],implementation_trust_zone='RH_FORMAL_CORE'),original[1]],
            [dict(original[0],specified_trust_zone='AUXILIARY_FORMALIZATION'),original[1]]]:
            with self.subTest(overrides=overrides):
                changed = copy.deepcopy(self.register)
                if overrides is None:
                    del changed['implementation_file_classification_overrides']
                else:
                    changed['implementation_file_classification_overrides'] = overrides
                self.assertTrue(any('exactly the two documented' in e for e in
                    contract.classification_errors(self.classes,self.manifest['modules'],changed)))

    def test_source_register_cannot_authorize_a_third_role_override(self):
        changed_classes = copy.deepcopy(self.classes)
        next(r for r in changed_classes['rules'] if r['id']=='opica_math')['trust_zone']='RH_FORMAL_CORE'
        changed_register = copy.deepcopy(self.register)
        changed_register['implementation_file_classification_overrides'].append({
            'path':'Zeta23/OPICA/WeightedLaplace.lean',
            'specified_trust_zone':'AUXILIARY_FORMALIZATION','implementation_trust_zone':'RH_FORMAL_CORE'})
        errors = contract.classification_errors(changed_classes,self.manifest['modules'],changed_register)
        self.assertTrue(any('exactly the two documented' in e for e in errors))
        self.assertIn('module classification mismatch: Zeta23/OPICA/WeightedLaplace.lean',errors)

    def test_native_adapters_cannot_reenter_frozen_legacy_candidate_population(self):
        changed = copy.deepcopy(self.classes)
        next(r for r in changed['rules'] if r['id']=='opica_native_adapters')['trust_zone']='RH_FORMAL_CORE'
        errors = contract.classification_errors(changed,self.manifest['modules'],self.register)
        self.assertEqual(sum('module classification mismatch: Zeta23/OPICA/Native' in e for e in errors),2)
        self.assertTrue(any('three permitted OPICA rules' in e for e in self.config_errors(classes=changed)))

    def test_frozen_manifest_native_semantic_roles_remain_required(self):
        changed = copy.deepcopy(self.manifest['modules'])
        for module in changed:
            if module['module']=='Zeta23.OPICA.NativeJetAdapter':
                module['trust_zone']='AUXILIARY_FORMALIZATION'
        errors = contract.classification_errors(self.classes,changed,self.register)
        self.assertIn('frozen native adapter specified trust zone changed: Zeta23/OPICA/NativeJetAdapter.lean',errors)

    def test_historical_archived_lean_stays_fixture(self):
        rule = self.classify('research/RHRC/integration/post290/review_execution_2026-10-14/local_components/Example.lean')
        self.assertEqual(rule['file_class'], 'RESEARCH_FIXTURE')
        self.assertEqual(rule['trust_zone'], 'AUDIT_ONLY')

    def test_generic_zeta_rule_cannot_capture_validation(self):
        path = 'Zeta23/OPICA/Validation.lean'
        good = self.classify(path)
        changed = [r for r in self.rules if r['id'] != 'opica_validation_audit']
        bad = next(r for r in changed if re.search(r['pattern'], path))
        self.assertEqual(good['trust_zone'], 'AUDIT_ONLY')
        self.assertNotEqual(bad['trust_zone'], 'AUDIT_ONLY')

    def test_all_historical_classifications_and_config_fields_unchanged(self):
        self.assertEqual(self.config_errors(),[])
        self.assertEqual(len(self.old_paths),2330)

    def test_changed_generic_rule_cannot_reclassify_historical_paths(self):
        changed = copy.deepcopy(self.classes)
        next(r for r in changed['rules'] if r['id']=='zeta_lean')['trust_zone'] = 'RH_FORMAL_CORE'
        errors = self.config_errors(classes=changed)
        self.assertTrue(any('immutable baseline objects/order' in e for e in errors))
        self.assertTrue(any('historical first-match classification changed' in e for e in errors))

    def test_historical_rule_objects_and_order_preserved(self):
        changed = copy.deepcopy(self.classes)
        changed['rules'][0],changed['rules'][1] = changed['rules'][1],changed['rules'][0]
        self.assertTrue(any('immutable baseline objects/order' in e for e in self.config_errors(classes=changed)))

    def test_only_three_exact_rule_insertions_are_allowed(self):
        changed = copy.deepcopy(self.classes)
        changed['rules'].append({'id':'extra','pattern':'^never-matches$',
            'file_class':'LEAN_SOURCE','trust_zone':'AUDIT_ONLY'})
        self.assertTrue(any('three permitted OPICA rules' in e for e in self.config_errors(classes=changed)))

    def test_old_standalone_role_cannot_be_changed_or_removed(self):
        old_name = next(iter(self.old_closure['standalone_module_roles']))
        for replacement in ['OPICA_GENERIC_FORMALIZATION',None]:
            with self.subTest(replacement=replacement):
                changed = copy.deepcopy(self.closure)
                if replacement is None:
                    del changed['standalone_module_roles'][old_name]
                else:
                    changed['standalone_module_roles'][old_name] = replacement
                self.assertTrue(any('immutable field/role' in e for e in self.config_errors(closure=changed)))

    def test_semantic_policy_cannot_be_changed_while_roles_are_appended(self):
        changed = copy.deepcopy(self.closure)
        changed['terminal_claim'] = 'RH_PROVED'
        self.assertTrue(any('immutable field/role' in e for e in self.config_errors(closure=changed)))

    def test_extra_or_wrong_new_role_is_rejected(self):
        changed = copy.deepcopy(self.closure)
        changed['standalone_module_roles']['Zeta23.OPICA.EXTRA'] = 'OPICA_GENERIC_FORMALIZATION'
        self.assertTrue(any('exactly the 26 OPICA roles' in e for e in self.config_errors(closure=changed)))


if __name__ == '__main__':
    unittest.main()
