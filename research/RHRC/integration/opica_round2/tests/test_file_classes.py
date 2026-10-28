"""Round2 has exact navigation roles and preserves all ancestor classifications."""
from __future__ import annotations
import copy
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[3]
GRAPH = REPO / 'research/RHRC/graph'
FROZEN = '416aec21d4d6634675639b5397cc300d1f826e34'
ROUND3_BASE = '775692f2e72d76b6a97cf66926a86cc96342c109'
ROUND3_BASE_TREE = 'acd548eb97ddaee68eb6c9df73f82756ee10d13f'
ROUND3_MATH = {'Zeta23/OPICARound3.lean', 'Zeta23/OPICARound3/All.lean'} | {
    'Zeta23/OPICARound3/'+name+'.lean' for name in ('NeutralParityCover', 'NeutralParityTopology',
        'CofinalSimultaneousNegative', 'UniformNeutralInterval', 'FirstNeutralCutoff',
        'KernelSafeSchur', 'FirstSimultaneousNegative', 'SchurNegativeWitness', 'NewbornSource')}
ROUND3_AUDIT = {'Zeta23/OPICARound3/Validation.lean', 'Zeta23/RHRC/OpicaRound3Bindings.lean',
                'Zeta23/RHRC/OpicaRound3AtlasExport.lean'} | {
    'Zeta23/OPICARound3/Validation/'+name+'.lean' for name in ('NeutralParityCover',
        'CofinalSimultaneousNegative', 'UniformNeutralInterval', 'FirstSimultaneousNegative',
        'NewbornSource')}
ROUND3_ROLES = {
    **{'Zeta23.OPICARound3.'+name: 'OPICA3_SOURCE_FAITHFUL_FORMAL_SUPPORT' for name in (
       'NeutralParityCover', 'NeutralParityTopology', 'CofinalSimultaneousNegative',
       'UniformNeutralInterval', 'FirstNeutralCutoff', 'FirstSimultaneousNegative', 'NewbornSource')},
    'Zeta23.OPICARound3.KernelSafeSchur': 'OPICA3_GENERIC_KERNEL_SAFE_LINEAR_ALGEBRA',
    'Zeta23.OPICARound3.SchurNegativeWitness': 'OPICA3_GENERIC_KERNEL_SAFE_LINEAR_ALGEBRA',
    **{name: 'OPICA3_INDEPENDENT_TYPE_AND_AXIOM_AUDIT' for name in (
       'Zeta23.OPICARound3.Validation', 'Zeta23.RHRC.OpicaRound3Bindings',
       'Zeta23.RHRC.OpicaRound3AtlasExport',
       'Zeta23.OPICARound3.Validation.NeutralParityCover',
       'Zeta23.OPICARound3.Validation.CofinalSimultaneousNegative',
       'Zeta23.OPICARound3.Validation.UniformNeutralInterval',
       'Zeta23.OPICARound3.Validation.FirstSimultaneousNegative',
       'Zeta23.OPICARound3.Validation.NewbornSource')},
    'Zeta23.OPICARound3': 'OPICA3_PHASE1_MATHEMATICAL_FACADE',
    'Zeta23.OPICARound3.All': 'OPICA3_PHASE1_MATHEMATICAL_FACADE',
}


def round3_rules():
    def rule(identity, paths, file_class, trust):
        return {'id': identity, 'pattern': r'\A(?:'+'|'.join(re.escape(p) for p in sorted(paths))+r')\Z',
                'file_class': file_class, 'trust_zone': trust}
    prefix = 'research/RHRC/integration/opica_round3/'
    return [rule('opica_round3_math', ROUND3_MATH, 'LEAN_SOURCE', 'AUXILIARY_FORMALIZATION'),
            rule('opica_round3_audit', ROUND3_AUDIT, 'LEAN_SOURCE', 'AUDIT_ONLY'),
            rule('opica_round3_configuration', {prefix+n+'.json' for n in (
                'DESCENDANT_EXTENSION', 'OPEN_RESEARCH', 'PUBLIC_ROOTS', 'SOURCE_REGISTER',
                'atlas/SEMANTIC_OVERLAY', 'schemas/constraint_atlas.schema',
                'schemas/source_evaluator.schema')},
                'BUILD_CONFIGURATION', 'AUDIT_ONLY'),
            rule('opica_round3_atlas_product', {prefix+'atlas/CONSTRAINT_ATLAS.jsonl'},
                'GENERATED_GRAPH_PRODUCT', 'AUDIT_ONLY'),
            rule('opica_round3_source_cases', {prefix+'fixtures/source_evaluator_cases.json'},
                'RESEARCH_FIXTURE', 'RESEARCH_ONLY'),
            rule('opica_round3_audit_executables', {prefix+n for n in (
                'validate_contract.py', 'constraint_atlas.py', 'source_backend.py',
                'source_evaluator.py', 'source_checker.py', 'tests/test_contract.py',
                'tests/test_constraint_atlas.py', 'tests/test_source_evaluator.py')},
                'RESEARCH_EXECUTABLE', 'AUDIT_ONLY'),
            rule('opica_round3_workflow', {'.github/workflows/rhrc_opica_round3.yml'}, 'CI_WORKFLOW', 'AUDIT_ONLY')]
sys.path.insert(0, str(GRAPH))
spec = importlib.util.spec_from_file_location('_opica2_class_graph', GRAPH/'build.py')
graph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(graph)


def frozen_json(relative, commit=FROZEN):
    return json.loads(subprocess.check_output(['git', 'show', commit+':'+relative], cwd=REPO))


class ExactRound2FileClasses(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.classes = json.loads((GRAPH/'FILE_CLASSES.json').read_text(encoding='utf-8'))
        cls.semantics = json.loads((GRAPH/'SEMANTIC_CLOSURE_CONFIG.json').read_text(encoding='utf-8'))
        cls.manifest = json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))
        cls.old_classes = frozen_json('research/RHRC/graph/FILE_CLASSES.json')
        cls.old_semantics = frozen_json('research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json')
        cls.round3 = (REPO/'research/RHRC/integration/opica_round3/DESCENDANT_EXTENSION.json').is_file()
        round4_manifest = REPO/'research/RHRC/integration/opica_round4/BUILD_MANIFEST.json'
        cls.round4 = json.loads(round4_manifest.read_text(encoding='utf-8')) if round4_manifest.is_file() else None
        cls.round4_rules = cls.round4['classification_rules'] if cls.round4 else []
        cls.round4_roles = cls.round4['standalone_module_roles'] if cls.round4 else {}
        if cls.round3:
            tree = subprocess.check_output(['git', 'rev-parse', ROUND3_BASE+'^{tree}'], cwd=REPO, text=True).strip()
            if tree != ROUND3_BASE_TREE:
                raise AssertionError('Exact reviewed Round3 base tree differs')
            cls.base_classes = frozen_json('research/RHRC/graph/FILE_CLASSES.json', ROUND3_BASE)
            cls.base_semantics = frozen_json('research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json', ROUND3_BASE)
        else:
            cls.base_classes, cls.base_semantics = cls.classes, cls.semantics
        cls.original_paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', FROZEN],
                                                     cwd=REPO, text=True).splitlines()
        cls.new_lean = {row['path'] for row in cls.manifest['create']
                        if row['path'].endswith('.lean') and (REPO/row['path']).is_file()}
        raw = subprocess.check_output(['git', 'ls-files', '-z'], cwd=REPO)
        paths = {p.decode('utf-8') for p in raw.split(b'\0') if p} | cls.new_lean
        if cls.round3:
            # Exact reviewed additions, never a broad filesystem glob/provider.
            paths |= ROUND3_MATH | ROUND3_AUDIT
        if cls.round4:
            paths |= {r['path'] for r in cls.round4['add'] if r['path'].endswith('.lean')}
        modules = {}
        for relative in paths:
            if graph.classify(relative, cls.classes)[0] in ('LEAN_SOURCE', 'LEAN_ROOT'):
                modules[graph.module_name(relative)] = relative
        imports = {name: graph.IMPORT_MODULES((REPO/path).read_text(encoding='utf-8'))
                   for name, path in modules.items()}
        local_imports = {name: [n for n in values if n in modules] for name, values in imports.items()}
        comparator = sorted(name for name, path in modules.items()
                            if path.startswith('comparator/') and path.count('/') == 1)
        cls.reachability = graph.reachability_view(local_imports, comparator)
        cls.modules, cls.local_imports = modules, local_imports

    def test_original_rule_objects_and_order_are_preserved(self):
        extra = [r for r in self.base_classes['rules'] if r['id'].startswith('opica_round2_')]
        self.assertEqual(self.base_classes['rules'], extra+self.old_classes['rules'])
        self.assertEqual(self.classes['rules'], self.round4_rules+(round3_rules() if self.round3 else [])+self.base_classes['rules'])
        current = {k: v for k, v in self.classes.items() if k != 'rules'}
        frozen = {k: v for k, v in self.old_classes.items() if k != 'rules'}
        self.assertEqual(current, frozen)

    def test_every_ancestor_path_keeps_its_original_classification(self):
        for path in self.original_paths:
            self.assertEqual(graph.classify(path, self.classes), graph.classify(path, self.old_classes), path)

    def test_every_declared_new_path_has_a_precise_round2_rule(self):
        self.assertEqual(len(self.manifest['create']), 102)
        for row in self.manifest['create']:
            cls, trust, rule = graph.classify(row['path'], self.classes)
            self.assertTrue(rule.startswith('opica_round2_'), row['path'])
            self.assertNotEqual(cls, 'UNKNOWN_FILE_CLASS')
            self.assertNotEqual(trust, 'UNKNOWN')

    def test_unlisted_future_paths_cannot_inherit_a_reviewed_round2_rule(self):
        for path in ('Zeta23/OPICARound2/Unlisted.lean',
                     'Zeta23/OPICARound2/Validation/Unlisted.lean',
                     'research/RHRC/integration/opica_round2/hidden_provider.py',
                     'research/RHRC/integration/opica_round2/fixtures/unlisted.json'):
            self.assertFalse(graph.classify(path, self.classes)[2].startswith('opica_round2_'), path)
        for path in ('Zeta23/OPICARound3/Unlisted.lean',
                     'Zeta23/OPICARound3/Validation/Unlisted.lean',
                     'research/RHRC/integration/opica_round3/UNLISTED.json'):
            self.assertFalse(graph.classify(path, self.classes)[2].startswith('opica_round3_'), path)

    def test_all_actual_audit_modules_remain_audit_only(self):
        for row in self.manifest['create']:
            if row['path'] in self.new_lean and row['role'] in ('LEAN_AUDIT', 'AUDIT_ONLY'):
                self.assertEqual(graph.classify(row['path'], self.classes)[:2], ('LEAN_SOURCE', 'AUDIT_ONLY'))

    def test_mathematics_is_supporting_formalization_without_terminal_promotion(self):
        for row in self.manifest['create']:
            if row['path'] in self.new_lean and row['role'] in ('LEAN_MATH', 'MATHEMATICAL_MINIMAL', 'MATHEMATICAL_FULL_CORE'):
                self.assertEqual(graph.classify(row['path'], self.classes)[:2],
                                 ('LEAN_SOURCE', 'AUXILIARY_FORMALIZATION'))
        self.assertEqual(self.semantics['terminal_claim'], 'RH_OPEN')
        self.assertIs(self.semantics['graph_theorem_promotion'], False)

    def test_every_old_semantic_object_is_preserved(self):
        for key, value in self.old_semantics.items():
            if key in ('standalone_module_roles', 'living_ssot_roles'):
                for name, role in value.items():
                    self.assertEqual(self.semantics[key].get(name), role, (key, name))
            else:
                self.assertEqual(self.semantics[key], value, key)

    def test_exact_actual36_module_dispositions_and_no_absent_optional_roles(self):
        old = self.old_semantics['standalone_module_roles']
        roles = self.semantics['standalone_module_roles']
        base_roles = self.base_semantics['standalone_module_roles']
        new = {k: v for k, v in base_roles.items() if k not in old}
        self.assertEqual(len(self.new_lean), 36)
        self.assertEqual(set(new), {graph.module_name(path) for path in self.new_lean})
        self.assertTrue(all(role.startswith('OPICA2_') for role in new.values()))
        self.assertEqual(roles, {**base_roles, **(ROUND3_ROLES if self.round3 else {}), **self.round4_roles})
        if self.round3:
            self.assertEqual(len(ROUND3_ROLES), 19)
            self.assertEqual(set(ROUND3_ROLES), {graph.module_name(p) for p in ROUND3_MATH | ROUND3_AUDIT})
        for row in self.manifest['create']:
            if row['path'].endswith('.lean') and not (REPO/row['path']).exists():
                self.assertNotIn(graph.module_name(row['path']), roles)

    def test_actual_global_reachability_matches_all_standalone_dispositions(self):
        self.assertEqual(set(self.reachability['standalone_or_auxiliary']),
                         set(self.semantics['standalone_module_roles']))

    def test_mathematical_facades_cannot_reach_audit_sources(self):
        for root in ('Zeta23.OPICARound2', 'Zeta23.OPICARound2.All'):
            pending, seen = [root], set()
            while pending:
                module = pending.pop()
                if module in seen:
                    continue
                seen.add(module)
                self.assertNotEqual(graph.classify(self.modules[module], self.classes)[1], 'AUDIT_ONLY', module)
                pending.extend(self.local_imports[module])

    def test_broad_mathematical_rule_cannot_swallow_independent_validation(self):
        bad = copy.deepcopy(self.classes)
        bad['rules'].insert(0, {'id':'bad_broad_math', 'pattern':r'^Zeta23/OPICARound2/.*\.lean$',
                              'file_class':'LEAN_SOURCE', 'trust_zone':'RH_FORMAL_CORE'})
        target = 'Zeta23/OPICARound2/Validation/CausalProbe.lean'
        self.assertNotEqual(graph.classify(target, bad)[:2], ('LEAN_SOURCE', 'AUDIT_ONLY'))
        self.assertEqual(graph.classify(target, self.classes)[:2], ('LEAN_SOURCE', 'AUDIT_ONLY'))

    def test_extra_standalone_disposition_does_not_close_the_census(self):
        bad = copy.deepcopy(self.semantics)
        bad['standalone_module_roles']['Zeta23.OPICARound2.Unlisted'] = 'OPICA2_SOURCE_FAITHFUL_FORMAL_SUPPORT'
        self.assertNotEqual(set(self.reachability['standalone_or_auxiliary']), set(bad['standalone_module_roles']))

    def test_round2_documents_have_navigation_roles_without_theorem_authority(self):
        roles = self.semantics['living_ssot_roles']
        self.assertEqual(roles['research/RHRC/integration/opica_round2/README.md'],
                         'OPICA2_IMPLEMENTATION_AND_RESEARCH_STATUS')
        self.assertEqual(roles['research/RHRC/integration/opica_round2/POST_GREEN_RESEARCH.md'],
                         'OPICA2_POST_GREEN_RESEARCH_RECORD')
        self.assertIs(self.semantics['graph_theorem_promotion'], False)


if __name__ == '__main__':
    unittest.main()
