"""Supplemental inputs cannot silently replace or expand frozen acceptance."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
import sys
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('followup_contract', HERE / 'validate_contract.py')
contract = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contract)


class FullReleaseLinkageTests(unittest.TestCase):
    def run_release(self, gate_result=None, gate_error=None):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp)/'release.json'
            argv = ['validate_contract.py','--phase','release','--formal-receipt',str(Path(tmp)/'receipt.json'),
                '--output',str(output)]
            basic = {'status':'PASS_PREPARATION_ONLY','errors':[],'release_ready':False,'RH':'OPEN','Step4':'OPEN'}
            with patch.object(sys,'argv',argv), patch.object(contract,'full_compiler_gate',
                    return_value=gate_result,side_effect=gate_error) as gate, \
                    patch.object(contract,'preflight',return_value=basic) as prep, patch('builtins.print'):
                code = contract.main()
                return code,json.loads(output.read_text(encoding='utf-8')),gate.call_count,prep.call_args

    def test_partial_receipt_failure_cannot_authorize_registered_extension(self):
        code,report,count,call = self.run_release(gate_error=ValueError('subset cannot satisfy full100'))
        self.assertEqual(code,1)
        self.assertEqual(count,1)
        self.assertFalse(call.kwargs['full_registry_verified'])
        self.assertIn('subset',report['errors'][0])
        self.assertFalse(report['release_ready'])

    def test_full_compiler_replay_does_not_discharge_other_release_companions(self):
        code,report,count,call = self.run_release(gate_result={
            'status':'FRESH_COMPILER_REPLAY_VERIFIED_FULL_100','release_ready':False})
        self.assertEqual(code,1)
        self.assertEqual(count,1)
        self.assertTrue(call.kwargs['full_registry_verified'])
        self.assertEqual(report['status'],'FAIL_RELEASE_INCOMPLETE')
        self.assertEqual(len(report['unwired_release_companions']),3)
        self.assertFalse(report['release_ready'])
        self.assertEqual((report['RH'],report['Step4']),('OPEN','OPEN'))


class FrozenAcceptanceTests(unittest.TestCase):
    def setUp(self):
        read = lambda name: json.loads((HERE / name).read_text(encoding='utf-8'))
        self.manifest, self.public, self.crosswalk, self.extension, self.register = map(read,
            ('BUILD_MANIFEST.json', 'PUBLIC_ROOTS.json', 'PAPER_CROSSWALK.json',
             'PARENT_EXTENSION.json', 'SOURCE_REGISTER.json'))
        # Preserve the original03 mutation fixtures at their historical version.
        if self.register['implementation_dependency_amendment']['id'] == 'DEP_2026_10_24_04':
            self.register['implementation_dependency_amendment'] = deepcopy(
                self.register['implementation_dependency_history'][2])
            self.register['implementation_dependency_history'] = self.register['implementation_dependency_history'][:2]
            self.register.pop('exact_source_extension_policy', None)
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


class ContinuationCheckpointTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.here = self.root / contract.CONTINUATION_FOLDER
        self.here.mkdir(parents=True)
        self.prefix = contract.CONTINUATION_ARTIFACT_PREFIX
        self.manifest_path = self.here / 'CONTINUATION_MANIFEST.json'
        self.document = {
            'schema': 'OPICA_CONTINUATION_CHECKPOINT_V1', 'id': 'CP_2026_10_22_01',
            'status': 'DRAFT_NO_FULL_ACCEPTANCE',
            'base_commit': '9b6a9a3a2badb4cff62a56c1158d9cef8759d30d',
            'parent_commit': 'd53dd70d38b0762af130b1d19b795af259f505f5',
            'original_primary_roots': 100, 'acceptance_units': 28,
            'frozen_public_roots_sha256': contract.FROZEN_SPEC['PUBLIC_ROOTS.json'],
            'release_ready': False, 'RH': 'OPEN', 'Step4': 'OPEN',
            'independent_closing_inequalities': 'OPEN', 'artifacts': [],
        }
        for name, data in [('AGENTS.md', b'draft agent instructions\n'),
                           (self.prefix + 'papers/foundation.md', b'reference only\n')]:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            self.document['artifacts'].append({'path': name, 'bytes': len(data),
                'sha256': hashlib.sha256(data).hexdigest()})
        self.document['artifacts'].sort(key=lambda row: row['path'])

    def write_manifest(self, data=None):
        encoded = (json.dumps(self.document, sort_keys=True).encode('utf-8')
                   if data is None else data)
        self.manifest_path.write_bytes(encoded)
        return hashlib.sha256(encoded).hexdigest()

    def check(self):
        pin = self.write_manifest()
        with patch.object(contract, 'CONTINUATION_MANIFEST_SHA256', pin):
            return contract.continuation_checkpoint(self.root, self.here)

    def reject(self):
        allowed, errors = self.check()
        self.assertEqual(allowed, set())
        self.assertTrue(errors)

    def test_exact_pinned_draft_artifacts_have_only_exact_exceptions(self):
        allowed, errors = self.check()
        self.assertEqual(errors, [])
        self.assertEqual(allowed, {contract.CONTINUATION_FOLDER + '/CONTINUATION_MANIFEST.json',
            'AGENTS.md', self.prefix + 'papers/foundation.md'})
        self.assertNotIn('Zeta23/OPICAFollowup/Validation.lean', allowed)

    def test_navigation_exceptions_are_exactly_seven_individually_pinned_documents(self):
        expected = frozenset({
            'AUDIT.md', 'FORK_NOTES.md',
            'research/RHRC/DOCUMENTATION_AUTHORITY.md',
            'research/RHRC/VALIDATION_PROTOCOL.md',
            'research/RHRC/graph/README.md',
            'research/RHRC/integration/README.md',
            'research/RHRC/graph/OPICA_FOLLOWUP_CURRENT_STATE.md',
        })
        self.assertIsInstance(contract.CONTINUATION_DOCUMENTATION_PATHS, frozenset)
        self.assertEqual(contract.CONTINUATION_DOCUMENTATION_PATHS, expected)
        for relative in expected:
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            data = ('Current routing only: ' + relative).encode()
            target.write_bytes(data)
            self.document['artifacts'].append({'path': relative, 'bytes': len(data),
                'sha256': hashlib.sha256(data).hexdigest()})
        self.document['artifacts'].sort(key=lambda row: row['path'])
        allowed, errors = self.check()
        self.assertEqual(errors, [])
        self.assertTrue(expected <= allowed)
        self.assertEqual(len(allowed), len(self.document['artifacts']) + 1)

    def test_missing_manifest_rejected(self):
        allowed, errors = contract.continuation_checkpoint(self.root, self.here)
        self.assertEqual(allowed, set())
        self.assertTrue(errors)

    def test_unpinned_manifest_cannot_refreeze_itself(self):
        self.write_manifest()
        with patch.object(contract, 'CONTINUATION_MANIFEST_SHA256', 'f' * 64):
            allowed, errors = contract.continuation_checkpoint(self.root, self.here)
        self.assertEqual(allowed, set())
        self.assertTrue(any('unreviewed' in error for error in errors))

    def test_every_scope_and_authority_field_remains_exact(self):
        for key, value in list(self.document.items()):
            if key == 'artifacts':
                continue
            with self.subTest(key=key):
                changed = 'PROVED' if isinstance(value, str) else 0
                self.document[key] = changed
                self.reject()
                self.document[key] = value

    def test_bool_integer_and_float_aliases_cannot_change_scope(self):
        for key, value in [('release_ready', 0), ('original_primary_roots', 100.0),
                           ('acceptance_units', 28.0)]:
            with self.subTest(key=key):
                original = self.document[key]
                self.document[key] = value
                self.reject()
                self.document[key] = original

    def test_malformed_json_and_duplicate_keys_rejected_even_with_honest_pin(self):
        for data in [b'{', b'[]', b'{"schema":"x","schema":"y"}']:
            with self.subTest(data=data):
                pin = self.write_manifest(data)
                with patch.object(contract, 'CONTINUATION_MANIFEST_SHA256', pin):
                    allowed, errors = contract.continuation_checkpoint(self.root, self.here)
                self.assertEqual(allowed, set())
                self.assertTrue(errors)

    def test_nonempty_record_inventory_required(self):
        for value in [[], None, {}, 'files']:
            with self.subTest(value=value):
                self.document['artifacts'] = value
                self.reject()

    def test_rows_require_exact_fields_and_types(self):
        original = deepcopy(self.document['artifacts'][0])
        for value in [None, {}, {**original, 'authority': 'PROVED'},
                      {**original, 'path': None}, {**original, 'bytes': True},
                      {**original, 'bytes': -1}, {**original, 'bytes': 1.0},
                      {**original, 'sha256': 'F' * 64}]:
            with self.subTest(value=value):
                self.document['artifacts'][0] = value
                self.reject()
        self.document['artifacts'][0] = original

    def test_parent_and_lean_sources_cannot_be_artifact_exceptions(self):
        row = self.document['artifacts'][0]
        for name in ['README.md', 'research/RHRC/README.md',
                     'research/RHRC/routes/R003_ccm_bridge/README.md',
                     'research/RHRC/graph/UNLISTED.md',
                     'Zeta23/OPICAFollowup/Validation.lean',
                     'Zeta23/OPICA/LocalData.lean',
                     contract.CONTINUATION_FOLDER + '/PUBLIC_ROOTS.json',
                     contract.CONTINUATION_FOLDER + '/tests/test_contract.py',
                     contract.CONTINUATION_FOLDER + '/continuation/2026-10-23/paper.md']:
            with self.subTest(name=name):
                row['path'] = name
                self.document['artifacts'].sort(key=lambda item: item['path'])
                self.reject()

    def test_unsafe_paths_rejected_within_the_allowed_prefix(self):
        for suffix in ['../escape', 'a/../b', './paper', 'a//b', 'a\\b',
                       'C:/x', 'a\n.md', '']:
            with self.subTest(suffix=suffix):
                self.document['artifacts'][-1]['path'] = self.prefix + suffix
                self.reject()

    def test_duplicate_unsorted_and_case_alias_records_rejected(self):
        rows = deepcopy(self.document['artifacts'])
        for changed in [[rows[1], rows[0]], [rows[0], deepcopy(rows[0]), rows[1]],
                        [rows[0], {**rows[0], 'path': 'agents.md'}, rows[1]]]:
            with self.subTest(paths=[row['path'] for row in changed]):
                self.document['artifacts'] = changed
                self.reject()

    def test_missing_or_changed_artifact_rejects_entire_exception(self):
        target = self.root / self.document['artifacts'][-1]['path']
        target.write_bytes(b'changed bytes\n')
        self.reject()
        target.unlink()
        self.reject()

    def test_false_length_or_digest_rejected(self):
        row = self.document['artifacts'][0]
        for key, value in [('bytes', row['bytes'] + 1), ('sha256', '0' * 64)]:
            with self.subTest(key=key):
                original = row[key]
                row[key] = value
                self.reject()
                row[key] = original

    def test_symlink_file_or_ancestor_flag_rejected(self):
        # Exercise the actual stat rejection branch without requiring native
        # Windows symlink privileges; this is not an OS symlink-creation test.
        pin = self.write_manifest()
        for marked in [self.manifest_path, self.root / 'AGENTS.md',
                       self.here / 'continuation']:
            with self.subTest(marked=marked), \
                 patch.object(contract, 'CONTINUATION_MANIFEST_SHA256', pin), \
                 patch.object(Path, 'is_symlink', lambda path: path == marked):
                allowed, errors = contract.continuation_checkpoint(self.root, self.here)
                self.assertEqual(allowed, set())
                self.assertTrue(any('symlink' in error for error in errors))

    def test_resolved_escape_rejected(self):
        pin = self.write_manifest()
        target = self.root / 'AGENTS.md'
        original_resolve = Path.resolve
        for destination in [self.root.parent / 'escaped.md',
                            self.root / 'Zeta23/OPICAFollowup/Validation.lean']:
            def resolve(path, *args, **kwargs):
                return destination if path == target else original_resolve(path, *args, **kwargs)
            with self.subTest(destination=destination), \
                 patch.object(contract, 'CONTINUATION_MANIFEST_SHA256', pin), \
                 patch.object(Path, 'resolve', resolve):
                allowed, errors = contract.continuation_checkpoint(self.root, self.here)
                self.assertEqual(allowed, set())
                self.assertTrue(any('escaped' in error for error in errors))

    def test_manifest_cannot_be_read_from_a_different_directory(self):
        self.write_manifest()
        allowed, errors = contract.continuation_checkpoint(self.root, self.root)
        self.assertEqual(allowed, set())
        self.assertTrue(errors)

    def test_preflight_exempts_verified_artifacts_but_never_grants_acceptance(self):
        # Other frozen-preflight branches have their own tests. This fixture
        # isolates inventory integration while calling the real checkpoint gate.
        protected = {'files': [], 'parent_head': 'parent', 'parent_tree': 'tree'}
        contexts = {'claim_registry': 'research/RHRC/CLAIM_REGISTRY.json',
                    'theorem_bindings': 'research/RHRC/REGISTERED_THEOREM_BINDINGS.json',
                    'file_classes': 'research/RHRC/graph/FILE_CLASSES.json',
                    'semantic_closure': 'research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json'}
        for key, relative in contexts.items():
            protected[key] = {}
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('{}')
        navigation = 'research/RHRC/graph/README.md'
        navigation_file = self.root / navigation
        navigation_bytes = b'New current routing header\nPreserved historical body\n'
        navigation_file.write_bytes(navigation_bytes)
        protected['files'].append({'path': navigation,
            'sha256': hashlib.sha256(b'Preserved historical body\n').hexdigest()})
        self.document['artifacts'].append({'path': navigation, 'bytes': len(navigation_bytes),
            'sha256': hashlib.sha256(navigation_bytes).hexdigest()})
        self.document['artifacts'].sort(key=lambda row: row['path'])
        data = json.dumps(protected).encode()
        (self.here / 'PROTECTED_STATE.json').write_bytes(data)
        for name, value in {
            'BUILD_MANIFEST.json': {'paper_sources': [], 'regression_sources': [], 'create': []},
            'PUBLIC_ROOTS.json': {'roots': [{}] * 100},
            'PAPER_CROSSWALK.json': {'scope_units': [{}] * 28},
            'PARENT_EXTENSION.json': {'modified_exact_paths': [], 'generated_exact_paths': []},
            'SOURCE_REGISTER.json': {},
        }.items():
            (self.here / name).write_text(json.dumps(value))
        for name in ['NormFirstTransfer.lean', 'Validation.lean']:
            path = self.root / 'Zeta23/OPICAFollowup' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('-- fixture')
        pin = self.write_manifest()
        expected = [row['path'] for row in self.document['artifacts']]
        expected.append(contract.CONTINUATION_FOLDER + '/CONTINUATION_MANIFEST.json')
        from types import SimpleNamespace
        with patch.object(contract, 'FROZEN_SPEC', {}), \
             patch.object(contract, 'FROZEN_PAPER', {}), \
             patch.object(contract, 'PROTECTED_SHA256', hashlib.sha256(data).hexdigest()), \
             patch.object(contract, 'CONTINUATION_MANIFEST_SHA256', pin), \
             patch.object(contract, 'metadata_errors', return_value=[]), \
             patch.object(contract, 'supplemental_errors', return_value=[]), \
             patch.object(contract, 'dependency_amendment_errors', return_value=[]), \
             patch.object(contract, 'candidate1_source_errors', return_value=[]), \
             patch.object(contract.subprocess, 'run') as run:
            run.return_value = SimpleNamespace(stdout=('\0'.join(expected) + '\0').encode())
            result = contract.preflight(self.root, self.here)
            self.assertEqual(result['errors'], [])
            self.assertEqual(result['status'], 'PASS_PREPARATION_ONLY')
            self.assertEqual((result['planned_roots'], result['coverage_units']), (100, 28))
            self.assertFalse(result['release_ready'])
            self.assertFalse(result['compiler_coverage_audited'])
            self.assertFalse(result['continuation_checkpoint']['formal_acceptance'])
            self.assertFalse(result['continuation_checkpoint']['proof_established_by_this_gate'])
            run.return_value = SimpleNamespace(stdout=('\0'.join(expected + ['rogue.md']) + '\0').encode())
            result = contract.preflight(self.root, self.here)
            self.assertTrue(any('unlisted files: rogue.md' in error for error in result['errors']))
            # Once the pinned doc bytes differ, the original parent protection
            # applies again. The constant whitelist is never a blanket bypass.
            navigation_file.write_bytes(b'Tampered current navigation\n')
            result = contract.preflight(self.root, self.here)
            self.assertTrue(any('continuation checkpoint rejected' in error for error in result['errors']))
            self.assertIn('protected parent changed: ' + navigation, result['errors'])
            self.assertFalse(result['release_ready'])


class ActualReleaseExecutionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.folder = Path(temporary.name)

    def test_failed_actual_process_retains_exact_log_and_command(self):
        with self.assertRaisesRegex(ValueError,'preserved evidence'):
            contract.execute_release_command(self.folder,[sys.executable,'-c',
                'print("real failure output"); raise SystemExit(7)'],self.folder,'actual-failure.log')
        receipt = contract.release_json(self.folder/'actual-failure.command.json')
        self.assertEqual(receipt['exit_code'],7)
        self.assertFalse(receipt['timed_out'])
        self.assertEqual(receipt['log_sha256'],hashlib.sha256((self.folder/'actual-failure.log').read_bytes()).hexdigest())
        self.assertIn(b'real failure output',(self.folder/'actual-failure.log').read_bytes())

    def test_actual_subprocess_cannot_inherit_foreign_test_repo_or_pythonpath(self):
        code = 'import json,os; print(json.dumps([os.getenv("OPICA_TEST_REPO"),os.getenv("PYTHONPATH")]))'
        with patch.dict(contract.os.environ,{'OPICA_TEST_REPO':'foreign','PYTHONPATH':'foreign'}):
            contract.execute_release_command(self.folder,[sys.executable,'-c',code],self.folder,'environment.log')
        self.assertEqual(contract.release_json(self.folder/'environment.log'),[None,None])

    def test_existing_success_log_cannot_be_reused(self):
        (self.folder/'reused.log').write_text('old successful output')
        with self.assertRaisesRegex(ValueError,'fresh release command'):
            contract.execute_release_command(self.folder,[sys.executable,'-c','pass'],self.folder,'reused.log')

    def test_command_timeout_retains_partial_output_and_rejects(self):
        error = contract.subprocess.TimeoutExpired(['python'],1,output=b'partial real output')
        with patch.object(contract.subprocess,'run',side_effect=error),self.assertRaises(ValueError):
            contract.execute_release_command(self.folder,['python'],self.folder,'timeout.log')
        self.assertTrue(contract.release_json(self.folder/'timeout.command.json')['timed_out'])
        self.assertEqual((self.folder/'timeout.log').read_bytes(),b'partial real output')

    def test_unittest_zero_skipped_expected_failure_and_duplicate_runs_rejected(self):
        for text in ['Ran 0 tests in 0.1s\n\nOK\n','Ran 10 tests in 0.1s\n\nOK (skipped=1)\n',
                'Ran 10 tests in 0.1s\n\nOK (expected failures=1)\n',
                'Ran 10 tests in 0.1s\nRan 10 tests in 0.1s\n\nOK\n',
                'Ran 10 tests in 0.1s\n\nFAILED (failures=1)\n']:
            with self.subTest(text=text):
                path = self.folder/'tests.log'; path.write_text(text)
                with self.assertRaises(ValueError): contract.require_complete_unittest_log(path)

    def test_successful_complete_unittest_log_is_counted(self):
        path = self.folder/'tests.log'; path.write_text('Ran 82 tests in 1.5s\n\nOK\n')
        self.assertEqual(contract.require_complete_unittest_log(path),82)

    def test_release_artifact_rejects_actual_symlink(self):
        target = self.folder/'real.json'; target.write_text('{}')
        link = self.folder/'link.json'
        link.symlink_to(target)
        with self.assertRaisesRegex(ValueError,'symlink'): contract.release_json(link)

    def test_release_artifact_rejects_actual_symlink_ancestor(self):
        target = self.folder/'real'; target.mkdir(); (target/'data.json').write_text('{}')
        link = self.folder/'link'; link.symlink_to(target,target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'symlink'): contract.release_json(link/'data.json')

    def test_release_json_rejects_duplicate_and_nonfinite_values(self):
        for value in ['{"status":"PASS","status":"FAIL"}','{"value":NaN}','{"value":Infinity}']:
            path = self.folder/'data.json'; path.write_text(value)
            with self.assertRaises(ValueError): contract.release_json(path)

    def test_incorrect_python_patch_is_rejected_from_actual_version_output(self):
        def execute(root,argv,output,name):
            (output/name).write_text('{"version":[3,13,4],"executable":"python"}')
            return {'exit_code':0}
        with patch.object(contract,'execute_release_command',side_effect=execute),self.assertRaisesRegex(ValueError,'3.13.5'):
            contract.python_runtime_identity(self.folder,'python',self.folder,'identity.log')

    def test_wrong_locked_wheel_bytes_fail_before_environment_creation(self):
        here = self.folder/'repo/research/RHRC/integration/opica_followup'; here.mkdir(parents=True)
        lock = HERE/'python-checks.lock'; (here/'python-checks.lock').write_bytes(lock.read_bytes())
        wheelhouse = self.folder/'supplied'; wheelhouse.mkdir()
        (wheelhouse/'sympy.whl').write_bytes(b'wrong wheel')
        (wheelhouse/'mpmath.whl').write_bytes(b'wrong wheel')
        output = self.folder/'execution'; output.mkdir()
        with patch.object(contract,'python_runtime_identity',return_value={'identity':{'version':[3,13,5]}}), \
                patch.object(contract,'execute_release_command') as execute,self.assertRaisesRegex(ValueError,'wheel bytes'):
            contract.fresh_locked_scientific_runtime(self.folder/'repo','python',output,wheelhouse=wheelhouse)
        execute.assert_not_called()

    def test_companion_missing_final_harvest_rejects_before_any_execution(self):
        from types import SimpleNamespace
        args = SimpleNamespace(parent_intake=self.folder/'parent.json',parent_formal_receipt=self.folder/'p0.json',
            workflow_harvest=None)
        with patch.object(contract,'load_release_intake') as load,self.assertRaisesRegex(ValueError,'completed final workflow'):
            contract.full_release_companions(args,self.folder/'output',root=self.folder/'repo')
        load.assert_not_called()


class FrozenReleaseArtifactTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(); self.addCleanup(temporary.cleanup)
        self.folder = Path(temporary.name)
        spec = importlib.util.spec_from_file_location('release_actual_replay_test',HERE/'replay_controls.py')
        self.replay = importlib.util.module_from_spec(spec); spec.loader.exec_module(self.replay)
        self.summary = {'schema':'OPICA_FOLLOWUP_REGRESSION_REPLAY_V1','status':'PASS_FROZEN_REGRESSION_ONLY',
            'python':'3.13.5','python313_runtime':True,'packages':{'sympy':'1.14.0','mpmath':'1.3.0'},
            'exact':[],'numerical':[],'interval_certified':False,'Lean_proof_authority':False,'RH':'OPEN','Step4':'OPEN'}
        statuses = {'p0':'PASS','round1':'PASS_FINITE_EXACT_CONTROLS_ONLY',
            'round2':'PASS_EXACT_ALGEBRA_CONTROLS_ONLY','final':'PASS_FINITE_EXACT_ONLY'}
        for label,path,count,digest in self.replay.EXACT:
            for mode in ['normal','optimized']:
                result = {'status':statuses[label],'python':'3.13.5','total_checks':count,
                    'script_sha256':digest,'optimized':mode=='optimized'}
                row = {'suite':label,'mode':mode,'expected_checks':count,'exit_code':0,'checker_sha256':digest,
                    'executed_script_sha256':digest,'result':result}
                self.record(row,label+'-'+mode+'.json'); self.summary['exact'].append(row)
        for label,path,digest in self.replay.NUMERIC:
            result = {'status':'PASS_NUMERICAL_CONSISTENCY_ONLY','interval_certified':False,
                'cases':{'copoisson':6,'round2':15,'final':12}[label],'script_sha256':digest}
            if label=='round2':
                result.update(status='PASS_NUMERICAL_CONSISTENCY_NOT_INTERVAL_CERTIFIED',
                    infinite_theorem_certification=False,new_Lean_roots=0,independent_review=False)
            row = {'suite':label,'exit_code':0,'checker_sha256':digest,'executed_script_sha256':digest,'result':result}
            self.record(row,'numeric-'+label+'.json'); self.summary['numerical'].append(row)

    def record(self,row,name):
        path = self.folder/name; path.write_text(json.dumps(row['result']))
        row['receipt_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        path.with_suffix('.log').write_text('Protocol fixture only, not scientific evidence.\n')

    def verify(self):
        return contract.verify_regression_summary(self.summary,artifacts=self.folder,replay=self.replay)

    def test_complete_protocol_fixture_verifies_eleven_actual_bound_artifacts(self):
        report = self.verify()
        self.assertEqual((report['exact_checks_per_mode'],report['numerical_cases']),(39920,33))
        self.assertEqual(len(report['artifacts']),11)
        self.assertFalse(report['Lean_proof_authority'])

    def test_summary_status_without_actual_artifacts_has_no_authority(self):
        with self.assertRaisesRegex(ValueError,'actual fresh regression'):
            contract.verify_regression_summary(self.summary)

    def test_missing_optimized_suite_rejected(self):
        self.summary['exact'].pop()
        with self.assertRaisesRegex(ValueError,'both complete'): self.verify()

    def test_duplicate_mode_cannot_replace_missing_suite(self):
        self.summary['exact'][-1] = deepcopy(self.summary['exact'][0])
        with self.assertRaisesRegex(ValueError,'both complete'): self.verify()

    def test_boolean_exit_code_and_count_do_not_alias_success(self):
        for key in ['exit_code']:
            original = self.summary['exact'][0][key]; self.summary['exact'][0][key] = False
            with self.assertRaises(ValueError): self.verify()
            self.summary['exact'][0][key] = original
        self.summary['exact'][0]['result']['total_checks'] = True
        with self.assertRaises(ValueError): self.verify()

    def test_numeric_authority_and_case_count_promotions_rejected(self):
        for label,key,value in [('round2','infinite_theorem_certification',True),
                ('copoisson','interval_certified',True),('final','cases',13)]:
            row = next(row for row in self.summary['numerical'] if row['suite']==label)
            original = row['result'][key]; row['result'][key] = value
            with self.assertRaises(ValueError): self.verify()
            row['result'][key] = original

    def test_stale_or_modified_actual_receipt_rejected(self):
        (self.folder/'round1-normal.json').write_text('{}')
        with self.assertRaisesRegex(ValueError,'artifact differs'): self.verify()

    def test_missing_actual_log_rejected(self):
        (self.folder/'numeric-final.log').unlink()
        with self.assertRaisesRegex(ValueError,'checker log missing'): self.verify()

    def test_receipt_bound_to_another_script_rejected(self):
        self.summary['exact'][0]['result']['script_sha256'] = '0'*64
        with self.assertRaises(ValueError): self.verify()


class CompleteReleaseCliLinkageTests(unittest.TestCase):
    def run_release(self, *, gate_error=None, companion_error=None, prep_errors=None,
                    change_receipt=False, companion_tree='b'*40):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp); formal = folder/'formal.json'; formal.write_text('{"actual":"protocol fixture"}')
            digest = hashlib.sha256(json.dumps(contract.release_json(formal),sort_keys=True,
                separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
            output = folder/'release.json'
            gate = {'status':'FRESH_COMPILER_REPLAY_VERIFIED_FULL_100','checked_commit':'a'*40,
                'checked_tree':'b'*40,'receipt_sha256':digest}
            companions = {'status':contract.RELEASE_COMPANIONS_STATUS,'checked_commit':'a'*40,'checked_tree':companion_tree}
            def run_companions(*args,**kwargs):
                if change_receipt: formal.write_text('{"changed":"after compiler"}')
                if companion_error: raise companion_error
                return companions
            argv = ['validate_contract.py','--phase','release','--formal-receipt',str(formal),'--output',str(output)]
            preflight = {'status':'PASS_PREPARATION_ONLY','errors':prep_errors or [],'release_ready':False,'RH':'OPEN','Step4':'OPEN'}
            with patch.object(sys,'argv',argv),patch.object(contract,'full_compiler_gate',return_value=gate,side_effect=gate_error), \
                    patch.object(contract,'preflight',return_value=preflight), \
                    patch.object(contract,'full_release_companions',side_effect=run_companions) as companion,patch('builtins.print'):
                code = contract.main()
            return code,contract.release_json(output),companion.call_count

    def test_success_requires_both_executed_gates_and_retains_open_claims(self):
        code,report,count = self.run_release()
        self.assertEqual((code,count),(0,1))
        self.assertEqual(report['status'],'PASS_FULL_FOLLOWUP_RELEASE')
        self.assertTrue(report['release_ready']); self.assertTrue(report['full_release_accepted'])
        self.assertEqual((report['RH'],report['Step4'],report['independent_closing_inequalities']),('OPEN','OPEN','OPEN'))
        self.assertEqual(report['independent_human_review'],'NOT_ESTABLISHED')

    def test_compiler_failure_cannot_reach_companion_execution(self):
        code,report,count = self.run_release(gate_error=ValueError('real compiler rejected'))
        self.assertEqual((code,count),(1,0)); self.assertFalse(report['full_release_accepted'])

    def test_preflight_failure_cannot_reach_companion_execution(self):
        code,report,count = self.run_release(prep_errors=['protected source changed'])
        self.assertEqual((code,count),(1,0)); self.assertFalse(report['release_ready'])

    def test_incomplete_summary_or_other_companion_failure_blocks_release(self):
        code,report,count = self.run_release(companion_error=ValueError('required summary unfinished'))
        self.assertEqual((code,count),(1,1)); self.assertFalse(report['release_ready'])
        self.assertIn('summary unfinished',' '.join(report['errors']))

    def test_source_identity_change_between_compiler_and_companions_rejected(self):
        code,report,count = self.run_release(companion_tree='c'*40)
        self.assertEqual(code,1); self.assertFalse(report['release_ready'])
        self.assertIn('identities differ',' '.join(report['errors']))

    def test_external_full_compiler_receipt_replacement_after_replay_rejected(self):
        code,report,count = self.run_release(change_receipt=True)
        self.assertEqual(code,1); self.assertFalse(report['release_ready'])
        self.assertIn('receipt changed',' '.join(report['errors']))


class FinalChildWorkflowExecutionTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location('release_original_harvester_test',HERE/'harvest_workflows.py')
        self.harvest = importlib.util.module_from_spec(spec); spec.loader.exec_module(self.harvest)
        self.head,self.tree = 'a'*40,'b'*40
        jobs,reviews = [],{}
        for index,(name,classification) in enumerate(self.harvest.CHILD_JOBS.items(),10):
            jobs.append({'id':index,'name':name,'run_id':1,'run_attempt':1,'head_sha':self.head,
                'status':'completed','conclusion':'success','steps':[]})
            reviews['1:1:'+str(index)] = {'run_id':1,'attempt':1,'head_sha':self.head,'event':'pull_request',
                'checked_sha':self.head,'checked_tree':self.tree,'classification':classification,
                'commands':[{'command':'protocol-fixture-command','exit_code':0}],
                'mathematical_disposition':'PROTOCOL_FIXTURE_ONLY_RH_OPEN'}
        self.raw = {'head_sha':self.head,'head_tree':self.tree,'commit_trees':{self.head:self.tree},
            'run_pages':[{'total_count':1,'workflow_runs':[{'id':1,'path':self.harvest.WORKFLOW,
                'event':'pull_request','head_sha':self.head,'run_attempt':1,'run_number':1,
                'status':'completed','conclusion':'success'}]}],
            'check_pages':[{'total_count':0,'check_runs':[]}],
            'job_pages':[{'run_id':1,'attempt':1,'pages':[{'total_count':len(jobs),'jobs':jobs}]}],
            'artifact_pages':[{'run_id':1,'pages':[{'total_count':0,'artifacts':[]}]}],
            'job_reviews':reviews}

    def verify(self):
        return contract.require_completed_child_workflow({'raw_collection':self.raw},self.harvest,self.head,self.tree)

    def test_all_original_ten_including_completed_summary_are_required(self):
        result = self.verify()
        self.assertEqual(result['scopes'][0]['original_required_job_instances'],10)

    def test_unfinished_summary_cannot_finish_its_own_release(self):
        summary = next(job for job in self.raw['job_pages'][0]['pages'][0]['jobs'] if job['name']=='followup-summary')
        summary.update(status='in_progress',conclusion=None)
        with self.assertRaisesRegex(ValueError,'followup-summary'): self.verify()

    def test_custom_policy_and_no_child_execution_cannot_create_release(self):
        self.raw['run_pages'][0]['workflow_runs'][0]['path'] = '.github/workflows/other.yml'
        self.raw['job_policies'] = [{'workflow':'.github/workflows/other.yml','event':'pull_request',
            'head_sha':self.head,'name':job['name'],'required':True,'classification':self.harvest.CHILD_JOBS[job['name']]}
            for job in self.raw['job_pages'][0]['pages'][0]['jobs']]
        with self.assertRaisesRegex(ValueError,'current-head child workflow execution is missing'): self.verify()

    def test_caller_policy_cannot_demote_a_formal_lane(self):
        self.raw['job_policies'] = self.harvest.default_policy(self.raw['run_pages'][0]['workflow_runs'],self.head)
        self.raw['job_policies'][0]['required'] = False
        with self.assertRaisesRegex(ValueError,'demoted'): self.verify()

    def test_unreviewed_required_output_rejected(self):
        self.raw['job_reviews'].pop('1:1:10')
        with self.assertRaisesRegex(ValueError,'unreviewed'): self.verify()

    def test_changed_source_tree_rejected(self):
        with self.assertRaisesRegex(ValueError,'head differs'):
            contract.require_completed_child_workflow({'raw_collection':self.raw},self.harvest,self.head,'c'*40)


class StrictPreparationProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location('release_exact_projection_fixture',HERE/'tests/test_exact_source_extension.py')
        cls.protocol = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = cls.protocol; spec.loader.exec_module(cls.protocol)
        cls.protocol.V2ExactPolicyTests.setUpClass()

    def fixture(self):
        fixture = self.protocol.V2ExactPolicyTests('test_valid_exact_subject_projection_preserves_every_parent_value')
        fixture.setUp()
        return fixture

    def test_actual_strict_protocol_context_can_project_only_unchanged_parent_metadata(self):
        fixture = self.fixture(); context = fixture.check()
        result = contract.exact_preparation_projection(context,fixture.old,HERE.parents[3])
        self.assertEqual(result,{key:fixture.old[key] for key in
            ('claim_registry','theorem_bindings','file_classes','semantic_closure')})

    def test_boolean_status_and_raw_contexts_cannot_authorize_preparation_projection(self):
        from types import SimpleNamespace
        for value in [True,False,None,{}, {'status':'VERIFIED'}, SimpleNamespace(parent_json=b'{}')]:
            with self.subTest(value=value),self.assertRaisesRegex(ValueError,'genuine strict'):
                contract.exact_preparation_projection(value,{},HERE.parents[3])

    def test_changed_old_claim_cannot_be_hidden_by_projection(self):
        fixture = self.fixture(); context = fixture.check()
        changed = deepcopy(fixture.old)
        changed['claim_registry']['claims'][0]['statement'] = 'Changed protected claim'
        with self.assertRaisesRegex(ValueError,'protected parent values'):
            contract.exact_preparation_projection(context,changed,HERE.parents[3])

    def test_malformed_policy_cannot_produce_strict_preparation_context(self):
        fixture = self.fixture(); fixture.policy['schema'] = 'CALLER_BOOLEAN_CONTEXT'
        with self.assertRaises((ValueError,KeyError,TypeError)):
            fixture.check()


class ExactDependencyAmendment04Tests(unittest.TestCase):
    """Protocol fixtures exercise actual validator functions, never grant authority."""
    def setUp(self):
        import types
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.folder = self.root / 'research/RHRC/integration/opica_followup'
        self.folder.mkdir(parents=True)
        self.manifest_bytes = (HERE / 'BUILD_MANIFEST.json').read_bytes()
        self.manifest = json.loads(self.manifest_bytes)
        (self.folder / 'BUILD_MANIFEST.json').write_bytes(self.manifest_bytes)
        self.register = json.loads((HERE / 'SOURCE_REGISTER.json').read_bytes())
        if self.register['implementation_dependency_amendment']['id'] == 'DEP_2026_10_21_03':
            self.register['implementation_dependency_history'].append(
                self.register['implementation_dependency_amendment'])
        self.snapshots, rows = [], []
        for plan in self.manifest['modules']:
            # Valid Lean import syntax is supplied as a finite exact fixture;
            # the real exact-policy provider separately parses actual sources.
            imports = ['Mathlib.Data.Fin.Basic', *plan['direct_project_imports']]
            source = ''.join('import ' + name + '\n' for name in imports).encode()
            target = self.root / plan['path']
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source)
            sha = hashlib.sha256(source).hexdigest()
            self.snapshots.append({'module':plan['module'], 'path':plan['path'],
                'source_sha256':sha, 'actual_all_ordered_imports':imports,
                'actual_direct_project_imports':plan['direct_project_imports'],
                'frozen_planned_project_imports':plan['direct_project_imports']})
            rows.append({'module':plan['module'], 'path':plan['path'], 'source_sha256':sha,
                'actual_all_ordered_imports':imports,
                'planned_direct_project_imports':plan['direct_project_imports'],
                'approved_direct_project_imports':plan['direct_project_imports'],
                'reason':'FIXTURE_ONLY exact ordered imports; no theorem or review authority.',
                'theorem_statement_changes':[], 'new_assumptions':[]})
        amendment = deepcopy(self.register['implementation_dependency_history'][2])
        amendment.update({'id':'DEP_2026_10_24_04','supersedes':'DEP_2026_10_21_03',
            'previous_amendment_sha256':contract.DEPENDENCY_V3_SHA256,'rows':rows})
        self.register['implementation_dependency_amendment'] = amendment
        self.register['exact_source_extension_policy'] = {
            'schema':'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V2', 'fixture_only':True}
        self.context = types.SimpleNamespace(policy_sha256=self.object_hash(
            self.register['exact_source_extension_policy']),
            subject_imports_json=self.canonical(self.snapshots))

    @staticmethod
    def canonical(value):
        return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()

    @classmethod
    def object_hash(cls, value):
        return hashlib.sha256(cls.canonical(value)).hexdigest()

    def write_register(self):
        (self.folder / 'SOURCE_REGISTER.json').write_bytes(self.canonical(self.register))

    def check(self, context='FIXTURE_ONLY_CONTEXT', write=True):
        if write:
            self.write_register()
        selected = self.context if context == 'FIXTURE_ONLY_CONTEXT' else context
        with patch.object(contract, 'exact_policy_context', return_value=selected):
            return contract.dependency_amendment_errors(self.register, self.manifest, self.root)

    def reject(self):
        self.assertTrue(self.check())

    def test_complete43_exact_snapshot_passes_protocol_only(self):
        self.assertEqual(self.check(), [])

    def test_missing_authenticated_context_cannot_fall_back(self):
        with patch.object(contract, '_dependency_amendment_errors_v3',
                          side_effect=AssertionError('forbidden legacy fallback')):
            self.assertTrue(self.check(context=None))

    def test_pending_real_anchor_fails_closed_without_mock(self):
        self.write_register()
        self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest, self.root))

    def test_rejected_authentication_cannot_fall_back(self):
        self.write_register()
        with patch.object(contract, 'exact_policy_context', side_effect=ValueError('PENDING_REVIEW')), \
                patch.object(contract, '_dependency_amendment_errors_v3',
                             side_effect=AssertionError('forbidden legacy fallback')):
            self.assertTrue(contract.dependency_amendment_errors(self.register, self.manifest, self.root))

    def test_unknown_version_cannot_fall_back(self):
        self.register['implementation_dependency_amendment']['id'] = 'DEP_2099_UNKNOWN'
        with patch.object(contract, '_dependency_amendment_errors_v3',
                          side_effect=AssertionError('forbidden legacy fallback')):
            self.reject()

    def test_caller_register_cannot_borrow_actual_policy_context(self):
        self.write_register()
        self.register['implementation_dependency_amendment']['rows'][0]['reason'] += ' forged'
        self.assertTrue(self.check(write=False))

    def test_frozen_manifest_source_bytes_cannot_change(self):
        with (self.folder / 'BUILD_MANIFEST.json').open('ab') as stream:
            stream.write(b'\n')
        self.reject()

    def test_supplied_manifest_cannot_rewrite_plan(self):
        self.manifest['modules'][0]['direct_project_imports'] = []
        self.reject()

    def test_policy_digest_cannot_be_forged(self):
        self.context.policy_sha256 = '0' * 64
        self.reject()

    def test_all43_rows_and_order_are_required(self):
        for change in ['drop', 'duplicate', 'reverse']:
            with self.subTest(change=change):
                original = deepcopy(self.register['implementation_dependency_amendment']['rows'])
                rows = self.register['implementation_dependency_amendment']['rows']
                if change == 'drop': rows.pop()
                elif change == 'duplicate': rows[-1] = deepcopy(rows[0])
                else: rows.reverse()
                self.reject()
                self.register['implementation_dependency_amendment']['rows'] = original

    def test_all43_authenticated_subjects_and_order_are_required(self):
        for rows in [self.snapshots[:-1], list(reversed(self.snapshots))]:
            with self.subTest(count=len(rows)):
                self.context.subject_imports_json = self.canonical(rows)
                self.reject()

    def test_changed_source_bytes_fail_after_authenticated_context(self):
        target = self.root / self.manifest['modules'][0]['path']
        target.write_bytes(target.read_bytes() + b'\n-- changed actual source\n')
        self.reject()

    def test_source_hash_is_not_a_caller_claim(self):
        self.register['implementation_dependency_amendment']['rows'][0]['source_sha256'] = '0' * 64
        self.reject()

    def test_mathlib_and_project_import_order_are_both_bound(self):
        rows = self.register['implementation_dependency_amendment']['rows']
        rows[0]['actual_all_ordered_imports'].reverse()
        self.reject()

    def test_unauthorized_project_import_and_frozen_plan_mutations_fail(self):
        for field in ['approved_direct_project_imports','planned_direct_project_imports']:
            with self.subTest(field=field):
                row = self.register['implementation_dependency_amendment']['rows'][0]
                original = deepcopy(row[field])
                row[field] = ['Zeta23.ForgedProof']
                self.reject()
                row[field] = original

    def test_complete_import_list_must_match_project_subset(self):
        snapshot = self.snapshots[0]
        snapshot['actual_all_ordered_imports'].append('Zeta23.ForgedProof')
        self.context.subject_imports_json = self.canonical(self.snapshots)
        self.register['implementation_dependency_amendment']['rows'][0]['actual_all_ordered_imports'] = snapshot['actual_all_ordered_imports']
        self.reject()

    def test_scope_claims_and_assumptions_are_preserved(self):
        amendment = self.register['implementation_dependency_amendment']
        for field, value in [('primary_roots',99),('acceptance_units',27),('new_paths',85),
                ('new_assumptions',['RH']),('theorem_statement_changes',['weakened']),
                ('promoted_supporting_lemmas',['optional']),('RH','PROVED'),('Step4','PROVED'),
                ('independent_closing_inequalities','PROVED'),('primary_roots',True)]:
            with self.subTest(field=field, value=value):
                old = amendment[field]
                amendment[field] = value
                self.reject()
                amendment[field] = old

    def test_all_three_historical_amendments_are_immutable_and_ordered(self):
        history = deepcopy(self.register['implementation_dependency_history'])
        for index in range(3):
            with self.subTest(index=index):
                self.register['implementation_dependency_history'][index]['new_assumptions'] = ['RH']
                self.reject()
                self.register['implementation_dependency_history'] = deepcopy(history)
        self.register['implementation_dependency_history'].reverse()
        self.reject()

    def test_row_domain_changes_and_blank_reasons_are_rejected(self):
        row = self.register['implementation_dependency_amendment']['rows'][0]
        for field, value in [('new_assumptions',['RH']),('theorem_statement_changes',['weaken']),('reason','  ')]:
            with self.subTest(field=field):
                old = row[field]
                row[field] = value
                self.reject()
                row[field] = old

    def test_unreviewed_extra_fields_are_rejected(self):
        self.register['implementation_dependency_amendment']['allow_scope_change'] = True
        self.reject()

    def test_duplicate_actual_register_json_key_is_rejected(self):
        self.write_register()
        path = self.folder / 'SOURCE_REGISTER.json'
        data = path.read_bytes()
        path.write_bytes(b'{"RH":"PROVED",' + data[1:])
        self.assertTrue(self.check(write=False))

    def test_missing_and_symlinked_actual_sources_are_rejected(self):
        target = self.root / self.manifest['modules'][0]['path']
        saved = target.read_bytes()
        target.unlink()
        self.reject()
        other = self.root / 'different-source.lean'
        other.write_bytes(saved)
        target.symlink_to(other)
        self.reject()




class Round2DescendantDispatchTests(unittest.TestCase):
    """Explicit ancestor replay cannot become current-tree acceptance."""
    def setUp(self):
        import types
        self.runtime = contract._round2_descendant_runtime(contract.REPO)
        self.inspection = {'status': 'PASS_SOURCE_SCOPE_ONLY', 'checked_commit': 'current'}
        self.projection = {'status': 'PASS_EXACT_FROZEN_SOURCE_ONLY', 'checked_commit': 'frozen'}
        self.raw = {'schema': 'OPICA_FOLLOWUP_PREPARATION_V1', 'status': 'PASS_PREPARATION_ONLY', 'errors': [],
                    'planned_roots': 100, 'RH': 'OPEN', 'Step4': 'OPEN'}
        self.types = types
        self.temp_root = contract.REPO.parent / 'opica-round2-test-temp'
        self.temp_root.mkdir(exist_ok=True)

    def replay(self, mutate=None, code=0, inspection_after=None):
        import types
        def runner(command, **kwargs):
            raw = dict(self.raw)
            if mutate:
                mutate(raw)
            Path(command[command.index('--output')+1]).write_text(json.dumps(raw), encoding='utf-8')
            self.assertEqual(kwargs['cwd'], self.source.resolve())
            self.assertEqual(command[2], 'research/RHRC/integration/opica_followup/validate_contract.py')
            self.assertIn('--phase', command)
            self.assertEqual(command[command.index('--phase')+1], 'preflight')
            self.assertNotIn('--ancestor-projection', command)
            return types.SimpleNamespace(returncode=code, stderr=b'original failure')
        with tempfile.TemporaryDirectory(dir=self.temp_root) as tmp:
            self.source = Path(tmp) / 'source'
            with patch.object(contract, '_round2_descendant_runtime', return_value=self.runtime), \
                 patch.object(self.runtime, 'inspect_descendant', side_effect=[self.inspection,
                    inspection_after if inspection_after is not None else self.inspection]), \
                 patch.object(self.runtime, 'verify_projection', return_value=self.projection), \
                 patch.object(contract.subprocess, 'run', side_effect=runner):
                return contract.descendant_preflight(contract.REPO, self.source)

    def test_static_success_retains_baseline_scope_and_zero_formal_authority(self):
        result = self.replay()
        self.assertEqual(result['status'], 'PASS_BASELINE_STATIC_ONLY')
        self.assertTrue(result['baseline_static_replay_accepted'])
        self.assertEqual(result['population'], 100)
        self.assertEqual(result['frozen_report'], self.raw)
        self.assertEqual(result['formal_acceptance'], 'NOT_CHECKED')
        for flag in ('baseline_replay_accepted', 'current_tree_compatibility_accepted',
                     'full_core_accepted', 'full_release_accepted'):
            self.assertIs(result[flag], False)
        self.assertEqual((result['RH'], result['Step4']), ('OPEN', 'OPEN'))

    def test_wrong_legacy_population_or_schema_never_becomes_pass(self):
        for mutate in (lambda r: r.update(planned_roots=100-1),
                       lambda r: r.update(schema='UNKNOWN'),
                       lambda r: r.update(status='PASS_FULL_RELEASE'),
                       lambda r: r.update(RH='PROVED')):
            with self.assertRaises(ValueError):
                self.replay(mutate)

    def test_original_cli_failure_is_not_hidden(self):
        with self.assertRaisesRegex(ValueError, 'unchanged frozen CLI rejected'):
            self.replay(code=1)

    def test_source_drift_during_original_replay_rejects(self):
        with self.assertRaisesRegex(ValueError, 'source identities changed'):
            self.replay(inspection_after={**self.inspection, 'checked_commit': 'different'})

    def test_unknown_extension_version_rejects_before_frozen_execution(self):
        with tempfile.TemporaryDirectory(dir=self.temp_root) as tmp:
            root = Path(tmp)
            here = root / 'research/RHRC/integration/opica_round2'
            here.mkdir(parents=True)
            for name in ('BUILD_MANIFEST.json', 'ANCESTOR_LOCK.json'):
                (here/name).write_bytes((self.runtime.HERE/name).read_bytes())
            extension = json.loads((self.runtime.HERE/'DESCENDANT_EXTENSION.json').read_text(encoding='utf-8'))
            extension['schema'] = 'UNKNOWN_DESCENDANT_VERSION'
            (here/'DESCENDANT_EXTENSION.json').write_text(json.dumps(extension), encoding='utf-8')
            with patch.object(contract, '_round2_descendant_runtime', return_value=self.runtime), \
                 patch.object(contract.subprocess, 'run') as run:
                with self.assertRaisesRegex(ValueError, 'Unknown extension version'):
                    contract.descendant_preflight(root, root/'source')
                run.assert_not_called()

    def test_wrong_projection_commit_rejects_before_execution(self):
        with tempfile.TemporaryDirectory(dir=self.temp_root) as tmp:
            root = Path(tmp)
            source = root/'source'
            source.mkdir()
            with patch.object(contract, '_round2_descendant_runtime', return_value=self.runtime), \
                 patch.object(self.runtime, 'inspect_descendant', return_value=self.inspection), \
                 patch.object(self.runtime.contract, 'git', return_value='wrong-head'), \
                 patch.object(contract.subprocess, 'run') as run:
                with self.assertRaisesRegex(ValueError, 'frozen Git source identity'):
                    contract.descendant_preflight(root, source)
                run.assert_not_called()

    def test_untracked_ignored_provider_census_rejects_before_execution(self):
        with tempfile.TemporaryDirectory(dir=self.temp_root) as tmp:
            root = Path(tmp)
            source = root/'source'
            source.mkdir()
            (source/'frozen.lean').write_bytes(b'theorem frozen : True := True.intro\n')
            (source/'hidden.py').write_bytes(b'pass\n')
            size, blob, digest = self.runtime.contract.actual_blob_identity(source/'frozen.lean')
            here = root/'research/RHRC/integration/opica_round2'
            here.mkdir(parents=True)
            row = {'path': 'frozen.lean', 'mode': '100644', 'git_blob': blob, 'bytes': size, 'sha256': digest}
            (here/'ANCESTOR_LOCK.json').write_text(json.dumps({'frozen_ancestor': {'source_manifest': [row]}}), encoding='utf-8')
            def git(_repo, *parts):
                if parts == ('rev-parse', 'HEAD'):
                    return self.runtime.contract.FROZEN_COMMIT
                if parts[0] == 'rev-parse':
                    return self.runtime.contract.FROZEN_TREE
                if parts[0] == 'status':
                    return ''
                if parts[0] == 'ls-tree':
                    return '100644 blob '+blob+'\tfrozen.lean'
                raise AssertionError(parts)
            with patch.object(contract, '_round2_descendant_runtime', return_value=self.runtime), \
                 patch.object(self.runtime, 'inspect_descendant', return_value=self.inspection), \
                 patch.object(self.runtime.contract, 'git', side_effect=git), \
                 patch.object(contract.subprocess, 'run') as run:
                with self.assertRaisesRegex(ValueError, 'Untracked or ignored source file'):
                    contract.descendant_preflight(root, source)
                run.assert_not_called()

    def test_every_original_predicate_body_is_byte_preserved(self):
        import ast
        import subprocess
        relative = 'research/RHRC/integration/opica_followup/validate_contract.py'
        baseline = subprocess.check_output(['git', 'show', self.runtime.contract.FROZEN_COMMIT+':'+relative],
                                           cwd=contract.REPO).decode('utf-8')
        current = (contract.REPO/relative).read_text(encoding='utf-8')
        old_nodes = {n.name: ast.get_source_segment(baseline, n) for n in ast.parse(baseline).body
                     if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name != 'main'}
        new_nodes = {n.name: ast.get_source_segment(current, n) for n in ast.parse(current).body
                     if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
        self.assertTrue(old_nodes)
        for name, source in old_nodes.items():
            self.assertEqual(new_nodes.get(name), source, name)


if __name__ == '__main__':
    unittest.main()
