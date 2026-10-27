"""Round2 has exact navigation roles and preserves all ancestor classifications."""
from __future__ import annotations
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parents[3]
GRAPH = REPO / 'research/RHRC/graph'
FROZEN = '416aec21d4d6634675639b5397cc300d1f826e34'
sys.path.insert(0, str(GRAPH))
spec = importlib.util.spec_from_file_location('_opica2_class_graph', GRAPH/'build.py')
graph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(graph)


def frozen_json(relative):
    return json.loads(subprocess.check_output(['git', 'show', FROZEN+':'+relative], cwd=REPO))


class ExactRound2FileClasses(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.classes = json.loads((GRAPH/'FILE_CLASSES.json').read_text(encoding='utf-8'))
        cls.semantics = json.loads((GRAPH/'SEMANTIC_CLOSURE_CONFIG.json').read_text(encoding='utf-8'))
        cls.manifest = json.loads((HERE/'BUILD_MANIFEST.json').read_text(encoding='utf-8'))
        cls.old_classes = frozen_json('research/RHRC/graph/FILE_CLASSES.json')
        cls.old_semantics = frozen_json('research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json')
        cls.original_paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', FROZEN],
                                                     cwd=REPO, text=True).splitlines()
        cls.new_lean = {row['path'] for row in cls.manifest['create']
                        if row['path'].endswith('.lean') and (REPO/row['path']).is_file()}
        raw = subprocess.check_output(['git', 'ls-files', '-z'], cwd=REPO)
        paths = {p.decode('utf-8') for p in raw.split(b'\0') if p} | cls.new_lean
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
        extra = [r for r in self.classes['rules'] if r['id'].startswith('opica_round2_')]
        self.assertEqual(self.classes['rules'], extra+self.old_classes['rules'])
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
        new = {k: v for k, v in roles.items() if k not in old}
        self.assertEqual(len(self.new_lean), 36)
        self.assertEqual(set(new), {graph.module_name(path) for path in self.new_lean})
        self.assertTrue(all(role.startswith('OPICA2_') for role in new.values()))
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
