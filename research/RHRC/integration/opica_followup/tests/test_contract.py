"""Supplemental inputs cannot silently replace or expand frozen acceptance."""
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

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
        for name in ['README.md', 'Zeta23/OPICAFollowup/Validation.lean',
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


if __name__ == '__main__':
    unittest.main()
