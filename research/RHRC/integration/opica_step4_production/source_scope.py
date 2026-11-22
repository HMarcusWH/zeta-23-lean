"""Exact common-pin preparation successor. Source acceptance is not Step 4 closure."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import unittest

from ..opica_composition.canonical import load_bytes, require, validate_path_inventory
from ..opica_composition.descendant import (
    MANIFEST, REPO, preserve_agent_instructions, preserve_documentation_renderer,
    validate_workflow_migration,
)
from ..opica_composition.snapshot import file_hash, unlinked
from ..documentation_2026_11_21 import source_scope as previous
from .runtime_profile import COMMON_ID, select_profile

PARENT = 'bb7c8184a135b2823c6296917c5ac893bebf2a71'
PARENT_TREE = '2b19357e1b65cc500f3e3a5b5d4df14601b02062'
PREFIX = 'research/RHRC/integration/opica_step4_production/'
POLICY = PREFIX + 'SOURCE_SCOPE.json'
VALIDATOR = PREFIX + 'source_scope.py'
POLICY_SHA256 = "dcd252d87881b6f8c960ac0a5068c41592c2e4ac0dc23802712d19f8cff60f53"
SCHEMA = 'OPICAS4_COMMON_PIN_SOURCE_INSPECTION_V1'
POLICY_SCHEMA = 'OPICAS4_COMMON_PIN_CLOSED_SOURCE_POLICY_V1'
PURPOSE = 'COMMON_PIN_PREPARATION_NOT_STEP4_ACCEPTANCE'
round6 = previous.round6
git = previous.git
blob = previous.blob


def check_policy(policy):
    fields = {'schema', 'parent', 'parent_tree', 'purpose', 'runtime_profile',
              'validator_template_sha256', 'added', 'edited', 'generated'}
    require(type(policy) is dict and set(policy) == fields, 'Unexpected common-pin policy fields')
    require((policy['schema'], policy['parent'], policy['parent_tree'], policy['purpose'],
             policy['runtime_profile']) == (POLICY_SCHEMA, PARENT, PARENT_TREE, PURPOSE, COMMON_ID),
            'Common-pin source policy authority or parent differs')
    require(type(policy['validator_template_sha256']) is str and
            round6.SHA256.fullmatch(policy['validator_template_sha256']), 'Unpinned successor validator')
    for field in ('added', 'edited'):
        require(type(policy[field]) is dict and all(type(v) is str and round6.SHA1.fullmatch(v)
                for v in policy[field].values()), 'Unpinned source operation: ' + field)
        validate_path_inventory(list(policy[field]))
    products = policy['generated']
    require(type(products) is list and products == sorted(set(products)) and
            all(p.startswith(round6.post299.GENERATED_ROOTS) and p.endswith(('.json', '.jsonl')) for p in products),
            'Unrecognized generated products')
    require(round6.FROZEN_PRODUCTS.isdisjoint([*products, *policy['edited']]), 'Frozen product changed')
    paths = [*policy['added'], *policy['edited'], *products, POLICY, VALIDATOR]
    require(len(paths) == len(set(paths)), 'Overlapping source operations')
    validate_path_inventory(paths)


def classify(parent, current, policy):
    check_policy(policy)
    added = set(current) - set(parent)
    require(added == set(policy['added']) | {POLICY, VALIDATOR}, 'Unlisted or missing successor addition')
    require(set(parent) <= set(current), 'Parent source deletion or rename')
    edited = {p for p in parent if parent[p] != current[p]}
    generated = edited & set(policy['generated'])
    require(set(policy['generated']) <= set(parent), 'Generated baseline path absent')
    require(edited - generated == set(policy['edited']), 'Unlisted or missing successor edit')
    for p in added | edited:
        require(current[p][:2] == ('100644', 'blob'), 'Nonregular successor source: ' + p)
        if p in parent: require(current[p][:2] == parent[p][:2], 'Source mode changed: ' + p)
    for p, expected in {**policy['added'], **policy['edited']}.items():
        require(current[p][2] == expected, 'Reviewed successor blob changed: ' + p)
    return {'added': sorted(added), 'edited': sorted(policy['edited']),
            'generated': sorted(generated), 'deleted': []}


def authenticate_parent(repo):
    """Replay unchanged historical pure checks against the parent Git objects."""
    require(git(repo, 'rev-parse', PARENT + '^{tree}').decode().strip() == PARENT_TREE,
            'Exact native parent tree differs')
    for revision, expected in ((previous.PARENT, previous.PARENT_TREE),
                               (previous.RESEARCH_PARENT, previous.RESEARCH_PARENT_TREE),
                               (round6.PARENT, round6.PARENT_TREE)):
        require(git(repo, 'rev-parse', revision + '^{tree}').decode().strip() == expected,
                'Historical baseline tree differs')
    for older, newer in ((round6.PARENT, previous.RESEARCH_PARENT),
                         (previous.RESEARCH_PARENT, previous.PARENT), (previous.PARENT, PARENT)):
        subprocess.run(['git', '-C', str(repo), 'merge-base', '--is-ancestor', older, newer], check=True)
    current = round6.tree(repo, PARENT)
    raw = blob(repo, current, previous.POLICY)
    require(hashlib.sha256(raw).hexdigest() == previous.POLICY_SHA256, 'Historical documentation policy changed')
    policy = load_bytes(raw); previous.check_policy(policy)
    research = round6.tree(repo, previous.RESEARCH_PARENT)
    archive = round6.tree(repo, previous.PARENT)
    inherited_raw = blob(repo, research, round6.POLICY)
    require(hashlib.sha256(inherited_raw).hexdigest() == round6.POLICY_SHA256, 'Historical Round 6 policy changed')
    inherited = load_bytes(inherited_raw)
    round6.classify(round6.tree(repo, round6.PARENT), research, inherited)
    require(round6.validator_template_hash(blob(repo, research, round6.VALIDATOR), round6.POLICY_SHA256) ==
            inherited['validator_template_sha256'], 'Historical Round 6 validator changed')
    previous.check_archive(research, archive, policy)
    previous.classify(archive, current, policy)
    require(round6.validator_template_hash(blob(repo, current, previous.VALIDATOR), previous.POLICY_SHA256) ==
            policy['validator_template_sha256'], 'Historical documentation validator changed')
    products = {r['path'] for r in load_bytes(blob(repo, archive, MANIFEST))['generated']}
    require(len(products) == 81 and products - round6.FROZEN_PRODUCTS == set(policy['generated']) and
            policy['generated'] == inherited['generated'], 'Inherited 77 active / four frozen products differ')
    for name in policy['edited']:
        if name.endswith('.md'):
            preserve_documentation_renderer(blob(repo, current, name), blob(repo, archive, name), path=name)
    if 'AGENTS.md' in policy['edited']:
        preserve_agent_instructions(blob(repo, current, 'AGENTS.md'), blob(repo, archive, 'AGENTS.md'))
    return current, policy


def inspect_committed_tree(repo=REPO, *, revision='HEAD'):
    """Git-object inspection only; an explicit revision is never worktree acceptance."""
    repo = unlinked(repo).resolve()
    observed_head = git(repo, 'rev-parse', 'HEAD').decode().strip()
    head = git(repo, 'rev-parse', revision + '^{commit}').decode().strip()
    current = round6.tree(repo, head)
    parent, parent_policy = authenticate_parent(repo)
    subprocess.run(['git', '-C', str(repo), 'merge-base', '--is-ancestor', PARENT, head], check=True)
    raw = blob(repo, current, POLICY)
    require(hashlib.sha256(raw).hexdigest() == POLICY_SHA256, 'Successor policy digest differs')
    policy = load_bytes(raw); check_policy(policy)
    require(policy['generated'] == parent_policy['generated'], 'Generated allowance changed')
    delta = classify(parent, current, policy)
    require(round6.validator_template_hash(blob(repo, current, VALIDATOR), POLICY_SHA256) ==
            policy['validator_template_sha256'], 'Successor validator template differs')
    runtime = select_profile(blob(repo, current, 'lean-toolchain'), blob(repo, current, 'lake-manifest.json'))
    require(runtime.identity == policy['runtime_profile'], 'Source pin tuple differs from successor policy')
    for name in policy['edited']:
        if name.endswith('.md'):
            preserve_documentation_renderer(blob(repo, current, name), blob(repo, parent, name), path=name)
    if 'AGENTS.md' in policy['edited']:
        preserve_agent_instructions(blob(repo, current, 'AGENTS.md'), blob(repo, parent, 'AGENTS.md'))
    require(observed_head == git(repo, 'rev-parse', 'HEAD').decode().strip(), 'Checkout head changed during inspection')
    return {'schema': SCHEMA, 'status': 'PASS_COMMITTED_TREE_SCOPE_ONLY',
            'checked_commit': head, 'checked_tree': git(repo, 'rev-parse', head + '^{tree}').decode().strip(),
            'base': PARENT, 'base_tree': PARENT_TREE, 'path_policy': POLICY_SHA256,
            'validator_blob': current[VALIDATOR][2], 'delta': delta, 'runtime_profile': runtime.record(),
            'canonical_product_count': 77, 'unchanged_historical_product_count': 4,
            'generated_freshness': 'SEPARATE_CANONICAL_CHECK_REQUIRED',
            'current_compiler_accepted': False, 'full_round4_accepted': False,
            'step4_receiver_accepted': False, 'joint_acceptance_established': False,
            'successor_human_review': 'PENDING', 'RH': 'OPEN', 'Step4': 'OPEN'}


def validate_descendant(repo=REPO, *, require_clean=False):
    repo = unlinked(repo).resolve()
    if POLICY not in round6.tree(repo, 'HEAD'):
        return previous.validate_descendant(repo, require_clean=require_clean)
    if require_clean:
        require(not git(repo, 'status', '--porcelain', '--untracked-files=all'), 'Dirty successor checkout')
    report = inspect_committed_tree(repo)
    previous.check_worktree(repo, round6.tree(repo, report['checked_commit']))
    validate_workflow_migration(repo)
    for raw in git(repo, 'ls-files', '-z', '--others', '--ignored', '--exclude-standard').split(b'\0'):
        name = raw.decode()
        require(not (name.startswith(('Zeta23/', 'research/', '.github/', 'docs/examples/')) and
                     name.endswith(('.lean', '.lean.in', '.py', '.yml', '.yaml'))), 'Ignored executable/source provider')
    require(report['checked_commit'] == git(repo, 'rev-parse', 'HEAD').decode().strip(), 'Source changed during qualification')
    if require_clean:
        require(not git(repo, 'status', '--porcelain', '--untracked-files=all'), 'Checkout changed during qualification')
    report['status'] = 'PASS_SOURCE_SCOPE_ONLY'
    report['manifest_sha256'] = file_hash(repo / MANIFEST)
    return report


def classification_rules(policy):
    paths = set(policy['added']) | {POLICY, VALIDATOR}
    groups = [('executable', sorted(p for p in paths if p.endswith('.py')), 'RESEARCH_EXECUTABLE'),
              ('configuration', sorted(p for p in paths if p.endswith('.json') and '/fixtures/' not in p), 'BUILD_CONFIGURATION'),
              ('fixture', sorted(p for p in paths if '/fixtures/' in p), 'RESEARCH_FIXTURE')]
    return [{'id': 'opica_step4_production_' + suffix,
             'pattern': r'\A(?:' + '|'.join(round6.re.escape(p) for p in names) + r')\Z',
             'file_class': kind, 'trust_zone': 'AUDIT_ONLY'} for suffix, names, kind in groups if names]


def check_classification():
    from ..opica_round2.tests.test_file_classes import ExactRound2FileClasses
    raw = (REPO / POLICY).read_bytes()
    require(hashlib.sha256(raw).hexdigest() == POLICY_SHA256, 'Classification source policy changed')
    policy = load_bytes(raw); check_policy(policy)
    old_policy = load_bytes((REPO / previous.POLICY).read_bytes())
    extra = classification_rules(policy) + previous.documentation_classification_rules(old_policy)

    class ExactStep4PreparationClasses(ExactRound2FileClasses):
        @classmethod
        def setUpClass(cls):
            super().setUpClass()
            require(cls.classes['rules'][:len(extra)] == extra, 'Exact successor classification prefix differs')
            roles = {'Zeta23.OPICARound5.ParityMomentBridge': 'OPICA5_PARITY_SEED_FORMAL_SUPPORT', **round6.ROLES}
            require(cls.round4 and cls.round4_roles.keys().isdisjoint(roles), 'Inherited roles overlap')
            require(all(cls.modules.get(name) == name.replace('.', '/') + '.lean' for name in roles), 'Inherited role subjects differ')
            cls.round4_roles = {**cls.round4_roles, **roles}
            cls.round4_rules = extra + cls.round4_rules

    return unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(ExactStep4PreparationClasses)).wasSuccessful()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--check-tree', action='store_true')
    mode.add_argument('--check-classification', action='store_true')
    args = parser.parse_args()
    if args.check_classification: return 0 if check_classification() else 1
    report = inspect_committed_tree() if args.check_tree else validate_descendant(require_clean=True)
    print(json.dumps(report, sort_keys=True, indent=2)); return 0


if __name__ == '__main__': raise SystemExit(main())
