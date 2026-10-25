"""Synthetic storage-policy protocol tests; fixtures never establish review authority."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import test_exact_source_extension as fixtures

candidate = fixtures.candidate
GENERATED = [
    'research/RHRC/graph/compiler/registered_dependencies/'
    'REGISTERED_DECLARATION_DEPENDENCIES-' + key + '.jsonl'
    for key in '0123456789abcdef']
IMPLEMENTATION = {
    '.github/workflows/rhrc.yml', '.github/workflows/rhrc_opica.yml',
    'research/RHRC/tools/lean_dependency_extract.py',
    'research/RHRC/graph/build.py', 'research/RHRC/graph/validate.py',
    'research/RHRC/integration/candidate_exactify.py',
    'research/RHRC/tools/query_dependencies.py', 'research/RHRC/ool/rhkg_phase_atlas.py'}


class StorageExtensionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixtures.V2ExactPolicyTests.setUpClass()

    def setUp(self):
        fixtures.V2ExactPolicyTests.setUp(self)
        self.v2 = deepcopy((self.raw, self.policy, self.anchor))
        self.descriptor = json.loads(self.contract['descriptor_bytes'])
        old = {row['path']:row for row in self.old['files']}
        files = {row['path']:row for row in self.raw['files']}
        edits = []
        for name in sorted(IMPLEMENTATION):
            original = deepcopy(old[name])
            current = files[name]
            payload = ('SYNTHETIC_STORAGE_IMPLEMENTATION_ONLY:' + name).encode()
            current.update(sha256=hashlib.sha256(payload).hexdigest(),
                           git_blob=hashlib.sha1(payload).hexdigest(), bytes=len(payload))
            edits.append({'original':original, 'current':deepcopy(current)})
        for name in GENERATED:
            payload = ('SYNTHETIC_GENERATED_SHARD:' + name).encode()
            self.raw['files'].append({'path':name, 'mode':'100644', 'bytes':len(payload),
                'sha256':hashlib.sha256(payload).hexdigest(), 'git_blob':hashlib.sha1(payload).hexdigest()})
        self.amendment = {
            'schema':'OPICA_REGISTERED_DEPENDENCY_STORAGE_AMENDMENT_V1',
            'id':'STORAGE_2026_10_25_01',
            'status':'IMPLEMENTATION_ONLY_NO_MATHEMATICAL_SCOPE_CHANGE',
            'authorization':'Do like we do with the other files and split them up?',
            'original_index_path':'research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl',
            'additional_generated_paths':deepcopy(GENERATED),
            'shard_key':'SHA256_UTF8_DECLARATION_FIRST_HEX_NIBBLE',
            'shard_count':16, 'maximum_shard_bytes':50*1024*1024,
            'row_schema_version':'RHKG-phase2b-compiler-dependencies-0.4',
            'index_schema':'RHKG_REGISTERED_DEPENDENCY_SHARDS_V1',
            'frozen_manifest_sha256':candidate.MANIFEST_SHA256,
            'original_projection_sha256':candidate.ORIGINAL_IMPLEMENTATION_SHA256,
            'original_generated_path_count':62, 'effective_generated_path_count':78,
            'preserved_dependency_channels':['TYPE','VALUE','STRUCTURE'],
            'primary_roots':100, 'acceptance_units':28,
            'theorem_statement_changes':[], 'new_assumptions':[], 'weakened_checks':[],
            'policy_grants_theorem_authority':False,
            'RH':'OPEN', 'Step4':'OPEN', 'independent_closing_inequalities':'OPEN',
            'protected_implementation_edits':edits}
        self.policy['schema'] = 'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V3'
        self.bind_amendment()

    check = fixtures.V2ExactPolicyTests.check
    reject = fixtures.V2ExactPolicyTests.reject
    reanchor_fixture = fixtures.V2ExactPolicyTests.reanchor_fixture

    def bind_amendment(self):
        # Explicit synthetic fixture reanchoring only. No real seal is written.
        self.policy['registered_dependency_storage_amendment'] = deepcopy(self.amendment)
        self.raw['registered_dependency_storage_amendment'] = deepcopy(self.amendment)
        self.policy['complete_path_mode_census'] = candidate.path_modes(self.raw['files'])
        self.reanchor_fixture()

    def file(self, name):
        return next(row for row in self.raw['files'] if row['path'] == name)

    def test_real_v3_predicate_preserves_all_four_parent_values(self):
        expected = {key:deepcopy(self.old[key]) for key in
                    ['claim_registry','theorem_bindings','file_classes','semantic_closure']}
        context = self.check()
        self.assertEqual(dict(candidate.project(context)), expected)
        self.raw['claim_registry']['claims'][0]['status'] = 'MUTATED_AFTER_VALIDATION'
        self.assertEqual(dict(candidate.project(context)), expected)

    def test_context_exposes_exact16_and_exact8_with_full_actual_inventory(self):
        context = self.check()
        self.assertEqual(context.generated_paths, frozenset(GENERATED))
        self.assertEqual(context.implementation_paths, frozenset(IMPLEMENTATION))
        self.assertEqual(context.actual_source_inventory_sha256, candidate.inventory_digest(self.raw['files']))
        self.assertEqual(context.storage_amendment_sha256, candidate.digest(candidate.canonical(self.amendment)))
        self.assertTrue(set(GENERATED) | IMPLEMENTATION <= context.exact_allowed_paths)

    def test_generated_contents_are_live_evidence_not_fixed_policy_seal(self):
        before = self.check()
        self.file(GENERATED[0]).update(bytes=99, sha256='c'*64, git_blob='c'*40)
        after = self.check()
        self.assertEqual(before.policy_sha256, after.policy_sha256)
        self.assertEqual(before.storage_amendment_sha256, after.storage_amendment_sha256)
        self.assertNotEqual(before.actual_source_inventory_sha256, after.actual_source_inventory_sha256)

    def test_protected_implementation_contents_remain_exactly_bound(self):
        self.file(sorted(IMPLEMENTATION)[0])['sha256'] = 'c'*64
        self.reject()

    def test_missing_generated_path_rejected_even_after_census_rebound(self):
        self.raw['files'] = [row for row in self.raw['files'] if row['path'] != GENERATED[-1]]
        self.bind_amendment(); self.reject()

    def test_seventeenth_unlisted_generated_path_cannot_use_folder_exemption(self):
        row = deepcopy(self.file(GENERATED[-1])); row['path'] += '.unlisted'
        self.raw['files'].append(row)
        self.bind_amendment(); self.reject()

    def test_case_aliased_generated_path_rejected(self):
        self.file(GENERATED[-1])['path'] = GENERATED[-1].upper()
        self.bind_amendment(); self.reject()

    def test_generated_mode_cannot_change_to_executable_or_symlink(self):
        self.file(GENERATED[-1])['mode'] = '100755'
        self.bind_amendment(); self.reject()
        self.file(GENERATED[-1])['mode'] = '120000'
        with self.assertRaisesRegex(ValueError, 'symlink or unsupported mode'):
            self.bind_amendment()

    def test_path_mode_census_cannot_omit_or_mutate_generated_subject(self):
        self.policy['complete_path_mode_census'] = [row for row in self.policy['complete_path_mode_census']
                                                   if row['path'] != GENERATED[-1]]
        self.reanchor_fixture(); self.reject()

    def test_duplicate_generated_identity_rejected(self):
        self.raw['files'].append(deepcopy(self.file(GENERATED[0])))
        with self.assertRaises(ValueError): self.bind_amendment()

    def test_amendment_missing_or_extra_path_rejected(self):
        original = deepcopy(self.amendment['additional_generated_paths'])
        for paths in [original[:-1], original+['extra.jsonl'], original[:-1]+[original[0]]]:
            with self.subTest(paths=paths):
                self.amendment['additional_generated_paths'] = paths
                self.bind_amendment(); self.reject()

    def test_generated_path_traversal_rejected(self):
        self.amendment['additional_generated_paths'][0] = '../escape.jsonl'
        self.bind_amendment(); self.reject()

    def test_missing_or_ninth_implementation_permission_rejected(self):
        original = deepcopy(self.amendment['protected_implementation_edits'])
        extra = deepcopy(original[0]); extra['original']['path'] = extra['current']['path'] = 'other.py'
        for edits in [original[:-1], original+[extra], original+[original[0]]]:
            with self.subTest(edits=len(edits)):
                self.amendment['protected_implementation_edits'] = edits
                self.bind_amendment(); self.reject()

    def test_implementation_original_current_pair_swap_rejected(self):
        row = self.amendment['protected_implementation_edits'][0]
        row['original'], row['current'] = row['current'], row['original']
        self.bind_amendment(); self.reject()

    def test_implementation_original_hash_cannot_repin_parent(self):
        self.amendment['protected_implementation_edits'][0]['original']['sha256'] = 'e'*64
        self.bind_amendment(); self.reject()

    def test_unchanged_tool_cannot_receive_unused_permission(self):
        row = self.amendment['protected_implementation_edits'][0]
        row['current'] = deepcopy(row['original'])
        current = self.file(row['current']['path']); current.clear(); current.update(row['current'])
        self.bind_amendment(); self.reject()

    def test_raw_register_amendment_must_equal_anchored_policy(self):
        self.raw['registered_dependency_storage_amendment']['maximum_shard_bytes'] += 1
        self.reject()

    def test_raw_amendment_numeric_alias_cannot_match_typed_trusted_policy(self):
        for key,value in [('shard_count',16.0),('primary_roots',100.0),
                          ('policy_grants_theorem_authority',0)]:
            with self.subTest(field=key):
                self.raw['registered_dependency_storage_amendment'] = deepcopy(self.amendment)
                self.raw['registered_dependency_storage_amendment'][key] = value
                self.reject()

    def test_missing_malformed_v3_never_falls_back_to_v2(self):
        self.policy.pop('registered_dependency_storage_amendment')
        self.reanchor_fixture()
        with patch.object(candidate, '_validate_policy_context_v2') as legacy:
            self.reject(); legacy.assert_not_called()

    def test_unknown_schema_never_falls_back_to_v2(self):
        self.policy['schema'] = 'OPICA_EXACT_SUBJECT_EXTENSION_POLICY_V999'
        self.reanchor_fixture()
        with patch.object(candidate, '_validate_policy_context_v2') as legacy:
            self.reject(); legacy.assert_not_called()

    def test_unconfigured_anchor_cannot_be_replaced_by_success_status(self):
        self.policy['status'] = 'APPROVED'
        with self.assertRaises(ValueError):
            candidate.validate_policy_context(self.raw,self.old,self.contract,
                candidate.canonical(self.policy),None,self.original)

    def test_unknown_amendment_field_rejected(self):
        self.amendment['approved_by_status_only'] = True
        self.bind_amendment(); self.reject()

    def test_channels_schema_partition_or_byte_limit_cannot_be_weakened(self):
        original = deepcopy(self.amendment)
        for key,value in [('preserved_dependency_channels',['TYPE','VALUE']),
                          ('row_schema_version','old-schema'),('shard_key','ANY_DIRECTORY'),
                          ('maximum_shard_bytes',100*1024*1024),('shard_count',15)]:
            with self.subTest(field=key):
                self.amendment = deepcopy(original); self.amendment[key] = value
                self.bind_amendment(); self.reject()

    def test_typed_scope_constants_cannot_be_float_or_integer_boolean_aliases(self):
        original = deepcopy(self.amendment)
        for key,value in [('shard_count',16.0),('primary_roots',100.0),
                          ('acceptance_units',28.0),('policy_grants_theorem_authority',0)]:
            with self.subTest(field=key):
                self.amendment = deepcopy(original); self.amendment[key] = value
                self.bind_amendment(); self.reject()

    def test_storage_amendment_cannot_change_mathematics_or_grant_authority(self):
        original = deepcopy(self.amendment)
        for key,value in [('theorem_statement_changes',['root80']),('new_assumptions',['RH']),
                          ('weakened_checks',['cold']),('primary_roots',99),('acceptance_units',27),
                          ('policy_grants_theorem_authority',True),('RH','PROVED'),('Step4','PROVED')]:
            with self.subTest(field=key):
                self.amendment = deepcopy(original); self.amendment[key] = value
                self.bind_amendment(); self.reject()

    def test_old_parent_claim_and_separate_gates_are_preserved(self):
        self.raw['claim_registry']['claims'][0]['status'] = 'PROVED_UNCONDITIONAL'
        self.reject()

    def test_storage_cannot_remove_original_release_gates(self):
        self.policy['separate_required_gates'] = []
        self.reanchor_fixture(); self.reject()

    def test_original_descriptor_and_generated62_are_immutable(self):
        descriptor = deepcopy(self.descriptor)
        descriptor['generated_exact_paths'].append(GENERATED[0])
        self.contract['descriptor_bytes'] = candidate.canonical(descriptor)
        self.policy['descriptor_sha256'] = candidate.digest(self.contract['descriptor_bytes'])
        self.reanchor_fixture(); self.reject()

    def test_unchanged_v2_still_uses_original_strict_projection(self):
        raw, policy, anchor = self.v2
        context = candidate.validate_policy_context(raw,self.old,self.contract,
            candidate.canonical(policy),anchor,self.original)
        self.assertEqual(context.generated_paths,frozenset())
        self.assertEqual(context.implementation_paths,frozenset())
        self.assertIsNone(context.storage_amendment_sha256)
        self.assertEqual(dict(candidate.project(context)),{key:self.old[key] for key in
            ['claim_registry','theorem_bindings','file_classes','semantic_closure']})


if __name__ == '__main__': unittest.main(verbosity=2)
