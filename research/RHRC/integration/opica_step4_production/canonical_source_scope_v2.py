"""Versioned live canonical index with an immutable, coherent historical snapshot.

This is source/storage qualification only. Original compiler/native gates remain
required; no result from this module promotes RH, Step 4, or a prior failed run.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import unittest

from ..opica_composition.canonical import load_bytes, require, validate_path_inventory
from ..opica_composition.descendant import MANIFEST, REPO, validate_workflow_migration
from ..opica_composition.snapshot import file_hash, unlinked
from . import source_scope as previous

PARENT = 'bf75a3a698c42852beda5c95669b06997559c4c0'
PARENT_TREE = '3d8200c0d972d313d70532c12a2a2909a5123cbc'
PREFIX = 'research/RHRC/integration/opica_step4_production/'
POLICY = PREFIX + 'CANONICAL_SOURCE_SCOPE_V2.json'
VALIDATOR = PREFIX + 'canonical_source_scope_v2.py'
HISTORY = PREFIX + 'HISTORICAL_REGISTERED_INDEX_V1.json'
TEST = PREFIX + 'test_canonical_source_scope_v2.py'
POLICY_SHA256 = "79e5b9b46617ad40bdc5db9ade8450667b6508572b8925adaf82e0a0f9ab5f57"
SCHEMA = 'OPICAS4_CANONICAL_INDEX_SOURCE_INSPECTION_V2'
POLICY_SCHEMA = 'OPICAS4_CANONICAL_INDEX_CLOSED_SOURCE_POLICY_V2'
PURPOSE = 'LIVE_CANONICAL_INDEX_WITH_IMMUTABLE_HISTORY_NOT_STEP4_ACCEPTANCE'
HISTORY_SCHEMA = 'OPICAS4_HISTORICAL_REGISTERED_STORAGE_V1'
INDEX = 'research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl'
INDEX_SHA256 = '12cc399f5c5b1154e95619f2da6d7f0df6e64b12d1292bafee67bbc335357917'
AUTHORED_ADDITIONS = frozenset({HISTORY, TEST})
AUTHORED_EDITS = frozenset({
    '.github/workflows/documentation.yml',
    'research/RHRC/graph/build.py',
    'research/RHRC/graph/FILE_CLASSES.json',
    'research/RHRC/integration/opica_composition/cli.py',
    'research/RHRC/integration/opica_composition/service.py',
    'research/RHRC/integration/opica_composition/tests/test_end_to_end.py',
})
round6 = previous.round6
git = previous.git
blob = previous.blob
DATED_HISTORY = frozenset(round6.FROZEN_PRODUCTS - {INDEX})


def _storage():
    path = Path(__file__).resolve().parents[1] / 'registered_dependency_shards.py'
    spec = importlib.util.spec_from_file_location('opicas4_original_registered_storage', path)
    require(spec is not None and spec.loader is not None, 'Original storage implementation unavailable')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


storage = _storage()


def scope_kind(head, tree, current):
    """Only the exact reviewed parent can use V1; absence is never a fallback."""
    if (head, tree) == (PARENT, PARENT_TREE):
        return 'EXACT_PARENT_V1'
    require(POLICY in current, 'A non-parent tree requires the explicit V2 policy')
    return 'EXPLICIT_V2'


def check_policy(policy, inherited_generated):
    fields = {'schema', 'parent', 'parent_tree', 'purpose', 'runtime_profile',
              'validator_template_sha256', 'history_descriptor_sha256',
              'added', 'edited', 'generated'}
    require(type(policy) is dict and set(policy) == fields, 'Unexpected canonical-index V2 policy fields')
    require((policy['schema'], policy['parent'], policy['parent_tree'], policy['purpose'],
             policy['runtime_profile']) == (POLICY_SCHEMA, PARENT, PARENT_TREE, PURPOSE, previous.COMMON_ID),
            'Canonical-index V2 authority, runtime or parent differs')
    for field in ('validator_template_sha256', 'history_descriptor_sha256'):
        require(type(policy[field]) is str and round6.SHA256.fullmatch(policy[field]),
                'Missing exact V2 digest: ' + field)
    require(type(policy['added']) is dict and set(policy['added']) == AUTHORED_ADDITIONS,
            'Unexpected canonical-index V2 additions')
    require(type(policy['edited']) is dict and set(policy['edited']) == AUTHORED_EDITS,
            'Unexpected canonical-index V2 authored edits')
    for field in ('added', 'edited'):
        require(all(type(value) is str and round6.SHA1.fullmatch(value)
                    for value in policy[field].values()), 'Unpinned V2 authored blob: ' + field)
    inherited = set(inherited_generated)
    require(len(inherited_generated) == len(inherited) == 77 and INDEX not in inherited
            and DATED_HISTORY.isdisjoint(inherited), 'Exact inherited 77 live products required')
    require(type(policy['generated']) is list and policy['generated'] == sorted(inherited | {INDEX}),
            'V2 permits only the original 77 live products plus their live index')
    paths = [*policy['added'], *policy['edited'], *policy['generated'], POLICY, VALIDATOR]
    require(len(paths) == len(set(paths)), 'Overlapping V2 source operations')
    validate_path_inventory(paths)


def classify(parent, current, policy, inherited_generated):
    check_policy(policy, inherited_generated)
    added = set(current) - set(parent)
    require(added == AUTHORED_ADDITIONS | {POLICY, VALIDATOR}, 'Unlisted or missing V2 addition')
    require(set(parent) <= set(current), 'Parent deletion or rename forbidden')
    edited = {path for path in parent if parent[path] != current[path]}
    generated = edited & set(policy['generated'])
    require(set(policy['generated']) <= set(parent), 'V2 generated path lacks a parent subject')
    require(edited - generated == AUTHORED_EDITS, 'Unlisted or missing V2 authored edit')
    require(all(current.get(path) == parent[path] for path in DATED_HISTORY),
            'Dated historical report changed')
    for path in added | edited:
        require(current[path][:2] == ('100644', 'blob'), 'Nonregular V2 subject: ' + path)
        if path in parent:
            require(current[path][:2] == parent[path][:2], 'V2 source mode changed: ' + path)
    for path, expected in {**policy['added'], **policy['edited']}.items():
        require(current[path][2] == expected, 'Reviewed V2 authored blob changed: ' + path)
    return {'added': sorted(added), 'edited': sorted(AUTHORED_EDITS),
            'generated': sorted(generated), 'deleted': []}


def check_history_descriptor(descriptor):
    fields = {'schema', 'repository', 'commit', 'tree', 'index_path', 'index_sha256',
              'index_schema', 'row_schema', 'logical_sha256', 'logical_bytes',
              'declaration_count', 'files', 'authority'}
    require(type(descriptor) is dict and set(descriptor) == fields, 'Historical descriptor fields differ')
    require((descriptor['schema'], descriptor['repository'], descriptor['commit'], descriptor['tree'],
             descriptor['index_path'], descriptor['index_sha256'], descriptor['index_schema'],
             descriptor['row_schema'], descriptor['authority']) ==
            (HISTORY_SCHEMA, 'HMarcusWH/zeta-23-lean', PARENT, PARENT_TREE, INDEX, INDEX_SHA256,
             storage.INDEX_SCHEMA, storage.ROW_SCHEMA, 'HISTORICAL_STORAGE_ONLY_NOT_CURRENT_COMPILER_ACCEPTANCE'),
            'Historical storage authority, identity or schema differs')
    require(type(descriptor['logical_sha256']) is str and round6.SHA256.fullmatch(descriptor['logical_sha256'])
            and type(descriptor['logical_bytes']) is int and descriptor['logical_bytes'] > 0
            and type(descriptor['declaration_count']) is int and descriptor['declaration_count'] > 0,
            'Historical logical receipt metadata invalid')
    files = descriptor['files']
    expected = sorted([INDEX, *storage.SHARD_PATHS])
    require(type(files) is list and len(files) == 17 and
            all(type(row) is dict and set(row) == {'path', 'git_blob', 'bytes', 'sha256'} for row in files)
            and [row['path'] for row in files] == expected, 'Exact ordered historical 17-object set required')
    for row in files:
        require(type(row['git_blob']) is str and round6.SHA1.fullmatch(row['git_blob'])
                and type(row['sha256']) is str and round6.SHA256.fullmatch(row['sha256'])
                and type(row['bytes']) is int and 0 < row['bytes'] <= storage.SHARD_MAX_BYTES,
                'Historical object metadata invalid')
    require(next(row for row in files if row['path'] == INDEX)['sha256'] == INDEX_SHA256,
            'Historical index digest differs')


def coherent_storage(read_bytes):
    """Use the unchanged strict reader; a self-consistent store is not a compiler proof."""
    raw = read_bytes(INDEX)
    index = storage._index(raw)
    require(index is not None, 'Current registered storage must be the explicit indexed representation')
    rows = storage.load_from_reader(lambda path: raw if path == INDEX else read_bytes(path))
    require(len(rows) == index['declaration_count'], 'Registered declaration count differs')
    return {'status': 'PASS_STORAGE_COHERENCE_ONLY', 'objects': 17,
            'index_sha256': hashlib.sha256(raw).hexdigest(),
            'logical_sha256': index['logical_sha256'], 'logical_bytes': index['logical_bytes'],
            'declaration_count': len(rows), 'fresh_compiler_acceptance': False}


def verify_historical_storage(parent, descriptor, read_blob):
    check_history_descriptor(descriptor)
    expected = {row['path']: row for row in descriptor['files']}

    def historical_read(path):
        require(path in expected, 'Historical reader requested an unlisted subject')
        row = expected[path]
        require(parent.get(path) == ('100644', 'blob', row['git_blob']),
                'Historical Git-object binding differs: ' + path)
        data = read_blob(row['git_blob'])
        require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'],
                'Historical object bytes differ: ' + path)
        return data

    result = coherent_storage(historical_read)
    require((result['index_sha256'], result['logical_sha256'], result['logical_bytes'], result['declaration_count']) ==
            (INDEX_SHA256, descriptor['logical_sha256'], descriptor['logical_bytes'], descriptor['declaration_count']),
            'Historical17 objects do not form the declared original logical receipt')
    return {**result, 'status': 'PASS_IMMUTABLE_HISTORICAL_17_OBJECTS_ONLY',
            'commit': PARENT, 'tree': PARENT_TREE, 'source': 'IMMUTABLE_GIT_OBJECTS_ONLY'}


def authenticate_parent(repo):
    # No altered historical validator or synthetic current-tree projection is used.
    report = previous.inspect_committed_tree(repo, revision=PARENT)
    require((report['checked_commit'], report['checked_tree'], report['schema']) ==
            (PARENT, PARENT_TREE, previous.SCHEMA), 'Exact common-pin V1 parent authentication failed')
    parent = round6.tree(repo, PARENT)
    raw = blob(repo, parent, previous.POLICY)
    require(hashlib.sha256(raw).hexdigest() == previous.POLICY_SHA256, 'Historical V1 policy differs')
    inherited = load_bytes(raw)
    previous.check_policy(inherited)
    return parent, inherited


def inspect_committed_tree(repo=REPO, *, revision='HEAD'):
    repo = unlinked(repo).resolve()
    observed = git(repo, 'rev-parse', 'HEAD').decode().strip()
    head = git(repo, 'rev-parse', revision + '^{commit}').decode().strip()
    tree = git(repo, 'rev-parse', head + '^{tree}').decode().strip()
    current = round6.tree(repo, head)
    if scope_kind(head, tree, current) == 'EXACT_PARENT_V1':
        return previous.inspect_committed_tree(repo, revision=PARENT)
    parent, inherited = authenticate_parent(repo)
    subprocess.run(['git', '-C', str(repo), 'merge-base', '--is-ancestor', PARENT, head], check=True)
    raw = blob(repo, current, POLICY)
    require(hashlib.sha256(raw).hexdigest() == POLICY_SHA256, 'V2 policy digest differs')
    policy = load_bytes(raw)
    delta = classify(parent, current, policy, inherited['generated'])
    require(round6.validator_template_hash(blob(repo, current, VALIDATOR), POLICY_SHA256) ==
            policy['validator_template_sha256'], 'V2 validator template differs')
    history_raw = blob(repo, current, HISTORY)
    require(hashlib.sha256(history_raw).hexdigest() == policy['history_descriptor_sha256'],
            'Historical17-object descriptor differs')
    historical = verify_historical_storage(parent, load_bytes(history_raw),
                                           lambda oid: git(repo, 'cat-file', 'blob', oid))
    current_storage = coherent_storage(lambda path: blob(repo, current, path))
    runtime = previous.select_profile(blob(repo, current, 'lean-toolchain'), blob(repo, current, 'lake-manifest.json'))
    require(runtime.identity == policy['runtime_profile'], 'V2 runtime tuple differs')
    require(observed == git(repo, 'rev-parse', 'HEAD').decode().strip(), 'Checkout head changed during V2 inspection')
    return {'schema': SCHEMA, 'status': 'PASS_COMMITTED_TREE_SCOPE_ONLY',
            'checked_commit': head, 'checked_tree': tree, 'base': PARENT, 'base_tree': PARENT_TREE,
            'path_policy': POLICY_SHA256, 'validator_blob': current[VALIDATOR][2], 'delta': delta,
            'runtime_profile': runtime.record(), 'canonical_product_count': 78,
            'unchanged_dated_historical_product_count': 3, 'historical_registered_storage': historical,
            'current_registered_storage': current_storage, 'generated_freshness': 'SEPARATE_CANONICAL_CHECK_REQUIRED',
            'current_compiler_accepted': False, 'full_round4_accepted': False, 'step4_receiver_accepted': False,
            'joint_acceptance_established': False, 'successor_human_review': 'PENDING', 'RH': 'OPEN', 'Step4': 'OPEN'}


def validate_descendant(repo=REPO, *, require_clean=False):
    repo = unlinked(repo).resolve()
    head = git(repo, 'rev-parse', 'HEAD').decode().strip()
    tree = git(repo, 'rev-parse', 'HEAD^{tree}').decode().strip()
    if scope_kind(head, tree, round6.tree(repo, head)) == 'EXACT_PARENT_V1':
        return previous.validate_descendant(repo, require_clean=require_clean)
    if require_clean:
        require(not git(repo, 'status', '--porcelain', '--untracked-files=all'), 'Dirty V2 checkout')
    report = inspect_committed_tree(repo)
    previous.previous.check_worktree(repo, round6.tree(repo, report['checked_commit']))
    validate_workflow_migration(repo)
    for raw in git(repo, 'ls-files', '-z', '--others', '--ignored', '--exclude-standard').split(b'\0'):
        name = raw.decode()
        require(not (name.startswith(('Zeta23/', 'research/', '.github/', 'docs/examples/')) and
                     name.endswith(('.lean', '.lean.in', '.py', '.yml', '.yaml'))), 'Ignored executable/source provider')
    require(report['checked_commit'] == git(repo, 'rev-parse', 'HEAD').decode().strip(), 'Source changed during V2 qualification')
    if require_clean:
        require(not git(repo, 'status', '--porcelain', '--untracked-files=all'), 'Checkout changed during V2 qualification')
    report['status'] = 'PASS_SOURCE_SCOPE_ONLY'
    report['manifest_sha256'] = file_hash(repo / MANIFEST)
    return report


def classification_rules():
    groups = [('executable', [TEST, VALIDATOR], 'RESEARCH_EXECUTABLE'),
              ('configuration', [POLICY], 'BUILD_CONFIGURATION'),
              ('historical_storage', [HISTORY], 'RESEARCH_RECEIPT')]
    return [{'id': 'opicas4_canonical_index_v2_' + suffix,
             'pattern': r'\A(?:' + '|'.join(round6.re.escape(path) for path in sorted(paths)) + r')\Z',
             'file_class': kind, 'trust_zone': 'AUDIT_ONLY'} for suffix, paths, kind in groups]


def check_classification():
    from ..opica_round2.tests.test_file_classes import ExactRound2FileClasses
    raw = (REPO / POLICY).read_bytes()
    require(hashlib.sha256(raw).hexdigest() == POLICY_SHA256, 'V2 classification policy changed')
    inherited_raw = (REPO / previous.POLICY).read_bytes()
    require(hashlib.sha256(inherited_raw).hexdigest() == previous.POLICY_SHA256, 'V1 classification policy changed')
    inherited = load_bytes(inherited_raw)
    check_policy(load_bytes(raw), inherited['generated'])
    docs = previous.previous
    doc_policy = load_bytes((REPO / docs.POLICY).read_bytes())
    extra = classification_rules() + previous.classification_rules(inherited) + docs.documentation_classification_rules(doc_policy)

    class ExactCanonicalIndexV2Classes(ExactRound2FileClasses):
        @classmethod
        def setUpClass(cls):
            super().setUpClass()
            require(cls.classes['rules'][:len(extra)] == extra, 'Exact V2 classification prefix differs')
            roles = {'Zeta23.OPICARound5.ParityMomentBridge': 'OPICA5_PARITY_SEED_FORMAL_SUPPORT', **round6.ROLES}
            require(cls.round4 and cls.round4_roles.keys().isdisjoint(roles), 'Inherited roles overlap')
            require(all(cls.modules.get(name) == name.replace('.', '/') + '.lean' for name in roles), 'Inherited role subjects differ')
            cls.round4_roles = {**cls.round4_roles, **roles}
            cls.round4_rules = extra + cls.round4_rules

    return unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(ExactCanonicalIndexV2Classes)).wasSuccessful()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--check-tree', action='store_true')
    modes.add_argument('--check-classification', action='store_true')
    args = parser.parse_args()
    if args.check_classification:
        return 0 if check_classification() else 1
    result = inspect_committed_tree() if args.check_tree else validate_descendant(require_clean=True)
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
