"""Adversarial compiler-delta tests; synthetic records have no theorem authority."""
from copy import deepcopy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
REPO = Path(os.environ.get('OPICA_TEST_REPO', HERE.parents[3])).resolve()
spec = importlib.util.spec_from_file_location('tested_followup_dependency_delta', HERE / 'dependency_delta.py')
delta = importlib.util.module_from_spec(spec); spec.loader.exec_module(delta)
child, parent = delta.load_builders(REPO)


def export_fixture():
    module = sorted(parent.MATHEMATICAL_MODULES)[0]
    name = 'Zeta23.OPICA.delta_fixture'
    expression = {'format': 'LEAN_EXPR_DAG_V1', 'root': '0', 'nodes': [['sort', ['zero']]]}
    encoded = json.dumps(expression, separators=(',', ':'))
    declaration = {'name': name, 'module': module, 'kind': 'THEOREM', 'axioms': [],
        'type_expression': expression, 'type_sha256': hashlib.sha256(encoded.encode()).hexdigest(),
        'type_metrics': parent.validate_expression(encoded)}
    private = '_private.' + module + '.0.delta_helper'
    metadata = [{'name': name, 'module': module, 'kind': 'THEOREM', 'internal': False},
        {'name': private, 'module': module, 'kind': 'THEOREM', 'internal': True},
        {'name': 'Real.delta_boundary_a', 'module': 'Mathlib.Fixture', 'kind': 'DEFINITION', 'internal': False},
        {'name': 'Real.delta_boundary_b', 'module': 'Mathlib.Fixture', 'kind': 'DEFINITION', 'internal': False}]
    edges = [{'source': n, 'channel': c, 'targets': targets} for n, c, targets in [
        (name, 'TYPE', ['Real.delta_boundary_a']), (name, 'VALUE', [private]), (name, 'STRUCTURE', []),
        (private, 'TYPE', []), (private, 'VALUE', ['Real.delta_boundary_b']), (private, 'STRUCTURE', [])]]
    return {'declarations': [declaration], 'constructors': {}, 'dependency_declarations': metadata, 'dependencies': edges}


class ParentCompilerDeltaTests(unittest.TestCase):
    def setUp(self): self.old = export_fixture(); self.current = deepcopy(self.old)
    def reject(self):
        with self.assertRaises(ValueError): delta.compare_parent_exports(self.old, self.current, parent)

    def test_equal_full_exports_preserve_parent_without_release_authority(self):
        result = delta.compare_parent_exports(self.old, self.current, parent)
        self.assertEqual(result['changed_parent_types'], [])
        self.assertNotIn('release_ready', result)

    def test_added_caller_hypothesis_is_detected_even_with_correct_new_dag_hash(self):
        row = self.current['declarations'][0]
        row['type_expression'] = {'format': 'LEAN_EXPR_DAG_V1', 'root': '1', 'nodes': [
            ['sort', ['zero']], ['forall', ['str', ['anonymous'], 'assumed_source_property'], 'default', '0', '0']]}
        encoded = json.dumps(row['type_expression'], separators=(',', ':'))
        row['type_sha256'] = hashlib.sha256(encoded.encode()).hexdigest()
        row['type_metrics'] = parent.validate_expression(encoded)
        self.reject()

    def test_changed_allowed_axioms_are_still_a_delta(self):
        self.current['declarations'][0]['axioms'] = ['Classical.choice']; self.reject()

    def test_sorry_and_project_axioms_are_rejected_before_comparison(self):
        for axiom in ['sorryAx', 'Zeta23.FixtureAxiom']:
            with self.subTest(axiom=axiom):
                self.current['declarations'][0]['axioms'] = [axiom]; self.reject()

    def test_private_helper_cannot_disappear(self):
        self.current['dependency_declarations'].pop(1); self.reject()

    def test_each_channel_is_required_including_structure(self):
        for channel in delta.CHANNELS:
            with self.subTest(channel=channel):
                self.current = deepcopy(self.old)
                self.current['dependencies'] = [r for r in self.current['dependencies'] if not
                    (r['source'].startswith('_private.') and r['channel'] == channel)]
                self.reject()

    def test_same_shared_nodes_do_not_hide_changed_type_edges(self):
        self.current['dependencies'][0]['targets'] = ['Real.delta_boundary_b']
        self.current['dependencies'][4]['targets'] = ['Real.delta_boundary_a']
        self.reject()

    def test_changed_structure_edge_is_not_hidden_by_same_union(self):
        self.current['dependencies'][2]['targets'] = ['Real.delta_boundary_a']; self.reject()

    def test_changed_origin_is_not_hidden_by_same_name(self):
        self.current['dependency_declarations'][-1]['module'] = 'Mathlib.OtherFixture'; self.reject()

    def test_duplicate_dependency_channel_is_rejected(self):
        self.current['dependencies'].append(deepcopy(self.current['dependencies'][0])); self.reject()

    def test_forged_type_digest_is_rejected(self):
        self.current['declarations'][0]['type_sha256'] = '0' * 64; self.reject()

    def test_forged_constructor_inventory_is_rejected(self):
        self.current['constructors']['Zeta23.OPICA.fakeConstructor'] = {}; self.reject()

    def test_matching_graphs_with_a_child_backedge_are_still_rejected(self):
        name = '_private.Zeta23.OPICAFollowup.Fixture.0.backedge'
        self.old['dependency_declarations'].append({'name': name,
            'module': 'Zeta23.OPICAFollowup.NativeFilters', 'kind': 'THEOREM', 'internal': True})
        self.old['dependencies'][4]['targets'] = [name]
        self.old['dependencies'] += [{'source': name, 'channel': c,
            'targets': ['Real.delta_boundary_b'] if c == 'VALUE' else []} for c in delta.CHANNELS]
        self.current = deepcopy(self.old)
        with self.assertRaisesRegex(ValueError, 'child dependency'):
            delta.compare_parent_exports(self.old, self.current, parent)

    def test_binder_inventory_reports_binders_without_inferring_premises(self):
        expression = {'format': 'LEAN_EXPR_DAG_V1', 'root': '1', 'nodes': [
            ['sort', ['zero']], ['forall', ['str', ['anonymous'], 'x'], 'implicit', '0', '0']]}
        result = delta.type_binder_inventory(expression, parent.validate_expression)
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0]['binder_info'], 'implicit')
        self.assertEqual(result[0]['classification'], 'EXPORTED_BINDER_NOT_AUTOMATICALLY_A_LOGICAL_PREMISE')

    def test_source_only_parent_capture_cannot_supply_p0_type_evidence(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)
            intake = path / 'source-intake.json'
            intake.write_bytes((REPO / 'research/RHRC/integration/opica_followup/PROTECTED_STATE.json').read_bytes())
            argv = ['dependency_delta.py', '--repo', str(REPO), '--parent-intake', str(intake),
                '--formal-receipt', str(path / 'absent-formal.json'), '--output', str(path / 'must-not-exist.json')]
            with patch.object(sys, 'argv', argv), self.assertRaisesRegex(ValueError, 'both.*P0 compiler receipts'):
                delta.main()
            self.assertFalse((path / 'must-not-exist.json').exists())


class FullChildUseDeltaTests(unittest.TestCase):
    def setUp(self):
        source = REPO / 'research/RHRC/integration/opica_followup/tests/test_receipt.py'
        spec = importlib.util.spec_from_file_location('delta_existing_full_receipt_fixtures', source)
        module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        self.fixture = module.FullReceiptTests('test_complete_synthetic_structure_has_no_release_authority')
        self.addCleanup(self.fixture.doCleanups)
        self.fixture.setUp()
        self.builder = module.receipt
        protected = json.loads((REPO / 'research/RHRC/integration/opica_followup/PROTECTED_STATE.json').read_text())
        self.bindings = protected['theorem_bindings']['bindings'] + [
            {'id': r['id'], 'theorem': r['full_name'], 'source': r['path']} for r in self.fixture.contract['roots']]

    def report(self, roots=None):
        return delta.child_use_report(self.fixture.data, roots if roots is not None else self.fixture.contract['roots'],
            self.bindings, self.builder, parent, modules=self.fixture.contract['export_modules'])

    def test_exact100_use_graph_never_claims_logical_equivalence(self):
        rows = self.report()
        self.assertEqual(len(rows), 100)
        self.assertTrue(all(r['logical_strength_or_equivalence'] == 'NOT_INFERRED_FROM_COMPILER_USES' for r in rows))

    def test_99_roots_cannot_claim_full_delta(self):
        with self.assertRaises(ValueError): self.report(self.fixture.contract['roots'][:-1])

    def test_missing_original_declaration_is_rejected(self):
        self.fixture.data['declarations'].pop(0)
        with self.assertRaises(ValueError): self.report()

    def test_duplicate_or_reused_registered_identity_is_rejected(self):
        self.bindings[-1]['id'] = self.bindings[0]['id']
        with self.assertRaises(ValueError): self.report()

    def test_swapped_theorem_bindings_cannot_change_registered_use_ids(self):
        self.bindings[-1]['theorem'], self.bindings[-2]['theorem'] = self.bindings[-2]['theorem'], self.bindings[-1]['theorem']
        with self.assertRaisesRegex(ValueError, 'identity/source differs'):
            self.report()


class ParentArtifactBindingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.folder = Path(self.tmp.name)
        exported = export_fixture(); row = exported['declarations'][0]
        root = {'id': 'SYNTHETIC_DELTA_TEST_ONLY', 'full_name': row['name'], 'module': row['module'],
            'kind': row['kind'], 'expected_type_sha256': row['type_sha256']}
        self.roots = [root]
        lines = ['\t'.join(['OPICA_DECL', row['name'], row['module'], row['kind'],
            json.dumps(row['type_expression'], separators=(',', ':')), '']),
            '\t'.join(['RHRC_CANDIDATE_RESULT', root['id'], 'RESOLVED_UNIQUE', '1', row['name'], row['module'],
                row['kind'], '0', 'SYNTHETIC TYPE NOT COMPILED', '-'])]
        lines += ['\t'.join(['RHKG_DEP_DECL', r['name'], r['module'], r['kind'], '1' if r['internal'] else '0'])
            for r in exported['dependency_declarations']]
        lines += ['\t'.join(['RHKG_DEP_CHANNEL', r['source'], r['channel'], *r['targets']]) for r in exported['dependencies']]
        wire = '\n'.join(lines + ['OPICA_PUBLIC_COUNT\t1', 'OPICA_COMPLETE\t1']) + '\n'
        parsed = parent.parse_compiler_output(wire, self.roots)
        self.manifest = {'base_commit': 'c' * 40, 'mathlib_commit': 'd' * 40,
            'no_root_api_pollution': {'required_build_targets': ['SYNTHETIC_TEST_ONLY']}}
        logs = {'lean-version.log': 'Lean (version 4.33.0-rc2, SYNTHETIC_NOT_EXECUTED)\n',
            'build.log': 'SYNTHETIC_NOT_EXECUTED\n', 'bindings.log': wire}
        commands = []
        for argv, name in [(['lake', 'env', 'lean', '--version'], 'lean-version.log'),
            (['lake', 'build', 'SYNTHETIC_TEST_ONLY'], 'build.log'),
            (['lake', 'env', 'lean', 'Zeta23/RHRC/OpicaBindings.lean'], 'bindings.log')]:
            payload = logs[name].encode(); (self.folder / name).write_bytes(payload)
            commands.append({'argv': argv, 'log': name, 'exit_code': 0, 'seconds': 0.0,
                'log_sha256': hashlib.sha256(payload).hexdigest()})
        self.data = {**parsed, 'schema': 'OPICA_COMPILER_RECEIPT_V1', 'status': 'COMPILER_VERIFIED',
            'checked_commit': 'a' * 40, 'requested_head': 'a' * 40, 'checked_tree': 'b' * 40,
            'requested_base': 'c' * 40, 'checkout_kind': 'PR_HEAD', 'mathlib_commit': 'd' * 40,
            'lean': logs['lean-version.log'].strip(), 'commands': commands}

    def test_complete_synthetic_artifacts_are_reparsed_without_acceptance_claim(self):
        self.assertIsNone(delta.verify_parent_artifacts(self.data, self.folder, parent, self.manifest, self.roots))

    def test_changed_real_log_bytes_cannot_be_hidden_behind_receipt_status(self):
        (self.folder / 'build.log').write_bytes(b'CHANGED')
        with self.assertRaisesRegex(ValueError, 'log hash differs'):
            delta.verify_parent_artifacts(self.data, self.folder, parent, self.manifest, self.roots)


if __name__ == '__main__': unittest.main()
