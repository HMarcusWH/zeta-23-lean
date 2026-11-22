"""Bounded V2 source/storage controls; no native compiler or theorem acceptance."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from ..opica_composition.canonical import ContractError
from . import canonical_source_scope_v2 as scope


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def small_storage(*, changed=False):
    # One synthetic row per shard: every immutable-object check is exercised.
    rows = {}; number = 0
    while len(rows) < 16:
        name = 'Fixture.declaration_' + str(number)
        key = scope.storage.shard_key(name)
        rows.setdefault(key, {
            'schema_version': scope.storage.ROW_SCHEMA, 'declaration': name,
            'module': 'Fixture', 'repository_scope': 'EXTERNAL',
            'graph_role': 'DEPENDENCY_BOUNDARY', 'declaration_kind': 'definition',
            'private_or_internal': False, 'dependencies': [],
        })
        number += 1
    values = list(rows.values())
    if changed:
        values[0]['dependencies'] = [{'constant': 'Fixture.changed', 'used_in_type': False,
                                     'used_in_value': True, 'used_in_structure': False}]
    return scope.storage.render_storage(values)


def synthetic_history(payload):
    index = scope.storage._index(payload[scope.INDEX])
    descriptor = {
        'schema': scope.HISTORY_SCHEMA, 'repository': 'HMarcusWH/zeta-23-lean',
        'commit': scope.PARENT, 'tree': scope.PARENT_TREE, 'index_path': scope.INDEX,
        'index_sha256': hashlib.sha256(payload[scope.INDEX]).hexdigest(),
        'index_schema': scope.storage.INDEX_SCHEMA, 'row_schema': scope.storage.ROW_SCHEMA,
        'logical_sha256': index['logical_sha256'], 'logical_bytes': index['logical_bytes'],
        'declaration_count': index['declaration_count'],
        'files': [{'path': p, 'git_blob': git_blob(payload[p]), 'bytes': len(payload[p]),
                   'sha256': hashlib.sha256(payload[p]).hexdigest()} for p in sorted(payload)],
        'authority': 'HISTORICAL_STORAGE_ONLY_NOT_CURRENT_COMPILER_ACCEPTANCE',
    }
    parent = {p: ('100644', 'blob', git_blob(data)) for p, data in payload.items()}
    objects = {git_blob(data): data for data in payload.values()}
    return descriptor, parent, objects


class CanonicalSourceV2Tests(unittest.TestCase):
    def setUp(self):
        self.old = ('100644', 'blob', '0' * 40)
        self.new = ('100644', 'blob', '1' * 40)
        directory = Path(__file__).parent
        self.inherited = json.loads((directory / 'SOURCE_SCOPE.json').read_bytes())['generated']
        self.protected = scope.PREFIX + 'source_scope.py'
        subjects = set(self.inherited) | scope.DATED_HISTORY | scope.AUTHORED_EDITS | {
            scope.INDEX, self.protected, scope.previous.POLICY,
            'research/RHRC/integration/registered_dependency_shards.py', 'lean-toolchain',
        }
        self.parent = {p: self.old for p in subjects}
        self.current = {**self.parent, **{p: self.new for p in
                        scope.AUTHORED_ADDITIONS | scope.AUTHORED_EDITS | {scope.POLICY, scope.VALIDATOR}}}
        self.policy = {
            'schema': scope.POLICY_SCHEMA, 'parent': scope.PARENT, 'parent_tree': scope.PARENT_TREE,
            'purpose': scope.PURPOSE, 'runtime_profile': scope.previous.COMMON_ID,
            'validator_template_sha256': 'a' * 64, 'history_descriptor_sha256': 'b' * 64,
            'added': {p: self.new[2] for p in scope.AUTHORED_ADDITIONS},
            'edited': {p: self.new[2] for p in scope.AUTHORED_EDITS},
            'generated': sorted(set(self.inherited) | {scope.INDEX}),
        }

    def test_exact_ten_authored_paths_and_live_index(self):
        result = scope.classify(self.parent, self.current, self.policy, self.inherited)
        self.assertEqual(len(result['added']) + len(result['edited']), 10)
        self.assertEqual(result['generated'], [])
        altered = {**self.current, scope.INDEX: self.new, scope.storage.SHARD_PATHS[0]: self.new}
        self.assertEqual(scope.classify(self.parent, altered, self.policy, self.inherited)['generated'],
                         sorted([scope.INDEX, scope.storage.SHARD_PATHS[0]]))

    def test_unknown_missing_mode_and_authored_hash_refused(self):
        mutations = {
            'unknown': {**self.current, scope.PREFIX + 'hidden.py': self.new},
            'missing-addition': {p: r for p, r in self.current.items() if p != scope.HISTORY},
            'missing-edit': {**self.current, next(iter(scope.AUTHORED_EDITS)): self.old},
            'deleted-parent': {p: r for p, r in self.current.items() if p != self.protected},
            'wrong-blob': {**self.current, scope.TEST: self.old},
            'symlink': {**self.current, scope.TEST: ('120000', 'blob', self.new[2])},
            'executable-mode': {**self.current, scope.TEST: ('100755', 'blob', self.new[2])},
            'new-generated': {**self.current, scope.INDEX + '.extra.json': self.new},
        }
        for label, current in mutations.items():
            with self.subTest(label=label), self.assertRaises(ContractError):
                scope.classify(self.parent, current, self.policy, self.inherited)

    def test_old_policy_storage_pins_and_dated_history_stay_frozen(self):
        paths = [*scope.DATED_HISTORY, self.protected, scope.previous.POLICY, 'lean-toolchain',
                 'research/RHRC/integration/registered_dependency_shards.py']
        for path in paths:
            with self.subTest(path=path), self.assertRaises(ContractError):
                scope.classify(self.parent, {**self.current, path: self.new}, self.policy, self.inherited)

    def test_exact_78_allowance_cannot_be_widened_or_reduced(self):
        bad = [self.policy['generated'][:-1], self.policy['generated'] + [scope.POLICY],
               sorted(self.policy['generated'] + [next(iter(scope.DATED_HISTORY))]),
               self.policy['generated'] + [scope.INDEX]]
        for generated in bad:
            with self.subTest(generated=generated[-1:]), self.assertRaises(ContractError):
                scope.check_policy({**self.policy, 'generated': generated}, self.inherited)
        with self.assertRaises(ContractError):
            scope.check_policy(self.policy, self.inherited[:-1])

    def test_policy_authority_parent_runtime_and_extra_claim_refused(self):
        values = [('parent', '4' * 40), ('parent_tree', '5' * 40), ('schema', 'OTHER'),
                  ('purpose', 'STEP4_CLOSED'), ('runtime_profile', 'ANY'),
                  ('history_descriptor_sha256', 'bad'), ('validator_template_sha256', 'bad'),
                  ('added', {}), ('edited', {})]
        for field, value in values:
            with self.subTest(field=field), self.assertRaises(ContractError):
                scope.check_policy({**self.policy, field: value}, self.inherited)
        with self.assertRaises(ContractError):
            scope.check_policy({**self.policy, 'RH': 'PROVED'}, self.inherited)

    def test_fallback_requires_exact_parent_commit_and_tree(self):
        self.assertEqual(scope.scope_kind(scope.PARENT, scope.PARENT_TREE, {}), 'EXACT_PARENT_V1')
        for head, tree in [(scope.PARENT, '8' * 40), ('9' * 40, scope.PARENT_TREE), ('9' * 40, '8' * 40)]:
            with self.subTest(head=head, tree=tree), self.assertRaises(ContractError):
                scope.scope_kind(head, tree, {})
        self.assertEqual(scope.scope_kind('9' * 40, scope.PARENT_TREE, {scope.POLICY: self.new}),
                         'EXPLICIT_V2')

    def test_nonparent_absent_policy_never_delegates_to_v1(self):
        def fake_git(repo, *args):
            return ((scope.PARENT_TREE if args[-1].endswith('^{tree}') else '9' * 40) + '\n').encode()
        with patch.object(scope, 'git', fake_git), patch.object(scope.round6, 'tree', return_value={}), \
                patch.object(scope.previous, 'inspect_committed_tree') as old:
            with self.assertRaises(ContractError):
                scope.inspect_committed_tree(Path(__file__).parent)
            old.assert_not_called()

    def test_exact_parent_fallback_delegates_to_immutable_revision(self):
        def fake_git(repo, *args):
            return ((scope.PARENT_TREE if args[-1].endswith('^{tree}') else scope.PARENT) + '\n').encode()
        with patch.object(scope, 'git', fake_git), patch.object(scope.round6, 'tree', return_value={}), \
                patch.object(scope.previous, 'inspect_committed_tree', return_value={'exact': True}) as old:
            result = scope.inspect_committed_tree(Path(__file__).parent)
            self.assertEqual(result, {'exact': True})
            self.assertEqual(old.call_args.kwargs, {'revision': scope.PARENT})

    def test_parent_authentication_rejects_wrong_historical_policy(self):
        report = {'checked_commit': scope.PARENT, 'checked_tree': scope.PARENT_TREE,
                  'schema': scope.previous.SCHEMA}
        with patch.object(scope.previous, 'inspect_committed_tree', return_value=report), \
                patch.object(scope.round6, 'tree', return_value={}), \
                patch.object(scope, 'blob', return_value=b'{"not":"the immutable V1 policy"}'):
            with self.assertRaises(ContractError):
                scope.authenticate_parent(Path(__file__).parent)

    def test_current_coherence_has_no_compiler_authority(self):
        for changed in (False, True):
            payload = small_storage(changed=changed)
            result = scope.coherent_storage(payload.__getitem__)
            self.assertEqual(result['status'], 'PASS_STORAGE_COHERENCE_ONLY')
            self.assertEqual(result['objects'], 17)
            self.assertEqual(result['declaration_count'], 16)
            self.assertIs(result['fresh_compiler_acceptance'], False)

    def test_old_index_new_shards_and_new_index_old_shards_rejected(self):
        old, new = small_storage(), small_storage(changed=True)
        for mixed in ({**new, scope.INDEX: old[scope.INDEX]}, {**old, scope.INDEX: new[scope.INDEX]}):
            with self.assertRaises(ValueError):
                scope.coherent_storage(mixed.__getitem__)

    def test_invalid_index_cannot_fall_back_to_monolithic(self):
        payload = small_storage()
        row = next(data.splitlines()[0] + b'\n' for p, data in payload.items()
                   if p != scope.INDEX and data)
        for raw in (b'{}', b'not JSON', b'', row):
            with self.subTest(raw=raw[:20]), self.assertRaises(ValueError):
                scope.coherent_storage({**payload, scope.INDEX: raw}.__getitem__)

    def test_logical_digest_count_and_shard_hash_drift_rejected(self):
        payload = small_storage()
        for field, value in [('logical_sha256', '0' * 64), ('declaration_count', 17), ('logical_bytes', 1)]:
            index = json.loads(payload[scope.INDEX]); index[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                scope.coherent_storage({**payload, scope.INDEX: json.dumps(index).encode()}.__getitem__)
        changed = {**payload, scope.storage.SHARD_PATHS[0]: payload[scope.storage.SHARD_PATHS[0]] + b'\n'}
        with self.assertRaises(ValueError):
            scope.coherent_storage(changed.__getitem__)

    def test_historical_reader_authenticates_all_17_immutable_objects(self):
        payload = small_storage(); descriptor, parent, objects = synthetic_history(payload)
        read = []
        def reader(oid):
            read.append(oid)
            return objects[oid]
        # Only this tiny fixture replaces the fixed historical digest. Production
        # constants and the delivered real descriptor are independently sealed.
        with patch.object(scope, 'INDEX_SHA256', descriptor['index_sha256']):
            result = scope.verify_historical_storage(parent, descriptor, reader)
        self.assertEqual(len(read), 17)
        self.assertEqual(set(read), set(objects))
        self.assertEqual(result['source'], 'IMMUTABLE_GIT_OBJECTS_ONLY')
        self.assertIs(result['fresh_compiler_acceptance'], False)

    def test_historical_blob_binding_missing_bytes_and_corruption_refused(self):
        payload = small_storage(); descriptor, parent, objects = synthetic_history(payload)
        path = scope.storage.SHARD_PATHS[0]; oid = parent[path][2]
        with patch.object(scope, 'INDEX_SHA256', descriptor['index_sha256']):
            with self.assertRaises(ContractError):
                scope.verify_historical_storage({**parent, path: self.new}, descriptor, objects.__getitem__)
            with self.assertRaises(KeyError):
                scope.verify_historical_storage(parent, descriptor, {k: v for k, v in objects.items() if k != oid}.__getitem__)
            with self.assertRaises(ContractError):
                scope.verify_historical_storage(parent, descriptor, {**objects, oid: objects[oid] + b'\n'}.__getitem__)

    def test_descriptor_rejects_alternate_history_inventory_or_authority(self):
        descriptor, _, _ = synthetic_history(small_storage())
        with patch.object(scope, 'INDEX_SHA256', descriptor['index_sha256']):
            for field, value in [('commit', '0' * 40), ('tree', '0' * 40), ('repository', 'other/repo'),
                                 ('index_sha256', '0' * 64), ('authority', 'CURRENT_ACCEPTED'),
                                 ('files', descriptor['files'][:-1]), ('declaration_count', True)]:
                with self.subTest(field=field), self.assertRaises(ContractError):
                    scope.check_history_descriptor({**descriptor, field: value})
            altered = copy.deepcopy(descriptor); altered['files'][0]['path'] = '../escape'
            with self.assertRaises(ContractError):
                scope.check_history_descriptor(altered)

    def test_self_consistent_changed_storage_still_needs_fresh_producer_match(self):
        expected = small_storage(); changed = small_storage(changed=True)
        scope.coherent_storage(changed.__getitem__)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path, data in changed.items():
                target = root / path; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
            with self.assertRaises(ValueError):
                scope.storage.check_storage(expected, root)

    def test_new_classification_rules_are_exact_and_audit_only(self):
        rules = scope.classification_rules()
        self.assertEqual(len(rules), 3)
        self.assertTrue(all(r['trust_zone'] == 'AUDIT_ONLY' for r in rules))
        for path in scope.AUTHORED_ADDITIONS | {scope.POLICY, scope.VALIDATOR}:
            self.assertEqual(sum(bool(scope.round6.re.search(r['pattern'], path)) for r in rules), 1)
        for path in (scope.PREFIX + 'unlisted.py', scope.PREFIX + 'unlisted.json', 'Zeta23/Unlisted.lean'):
            self.assertFalse(any(scope.round6.re.search(r['pattern'], path) for r in rules))

    def test_sealed_delivered_policy_template_and_real_history_descriptor(self):
        root = Path(__file__).resolve().parents[4]
        raw = (root / scope.POLICY).read_bytes(); policy = json.loads(raw)
        self.assertEqual(hashlib.sha256(raw).hexdigest(), scope.POLICY_SHA256)
        scope.check_policy(policy, self.inherited)
        self.assertEqual(scope.round6.validator_template_hash((root / scope.VALIDATOR).read_bytes(), scope.POLICY_SHA256),
                         policy['validator_template_sha256'])
        history = (root / scope.HISTORY).read_bytes(); descriptor = json.loads(history)
        scope.check_history_descriptor(descriptor)
        self.assertEqual(hashlib.sha256(history).hexdigest(), policy['history_descriptor_sha256'])
        self.assertEqual(descriptor['index_sha256'], '12cc399f5c5b1154e95619f2da6d7f0df6e64b12d1292bafee67bbc335357917')
        self.assertEqual(descriptor['declaration_count'], 22198)
        for path, oid in {**policy['added'], **policy['edited']}.items():
            self.assertEqual(git_blob((root / path).read_bytes()), oid, path)


if __name__ == '__main__':
    unittest.main()
