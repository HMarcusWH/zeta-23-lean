"""Authenticated frozen-source projections; baseline replay is a separate scope.

The old predicates execute unchanged in a detached checkout of the actual
frozen commit. This does not certify their current-tree compatibility.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from typing import Any

try:
    from .certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json
    from . import validate_contract as contract
except ImportError:
    from certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json
    import validate_contract as contract

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
# Audited 90 required + 12 optional new paths, 15 authorized edits, 81 exact
# generated products. A candidate manifest cannot enlarge its own authority.
AUDITED_PATH_POLICY = '01b7668bcb005c28cbeb86b87907a6f4ef6749bc31b33329ba1a96fdfcecc435'


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate('ancestor_projection', message)


def path_policy(manifest: dict[str, Any]) -> dict[str, list[str]]:
    result = {}
    for key in ('create', 'edit', 'generated'):
        rows = manifest.get(key)
        require(type(rows) is list, 'Missing exact path inventory: '+key)
        result[key] = sorted(contract.safe_relative(row['path']) for row in rows)
        require(len(result[key]) == len(set(result[key])), 'Duplicate policy path')
    encoded = json.dumps(result, sort_keys=True, separators=(',', ':')).encode('utf-8')
    require(hashlib.sha256(encoded).hexdigest() == AUDITED_PATH_POLICY,
            'The audited descendant path policy changed')
    require(not (set(result['create']) & (set(result['edit']) | set(result['generated']))),
            'New and ancestor path scopes overlap')
    return result


def inspect_descendant(repo: Path = REPO, here: Path = HERE) -> dict[str, Any]:
    repo, here = repo.resolve(), here.resolve()
    child = contract.round3_extension_context(repo)
    if child is not None:
        # The child authenticates every unchanged775 byte and its exact reviewed
        # delta. Original416 projection verification below is never widened.
        manifest = load_strict_json(here/'BUILD_MANIFEST.json', 8*1024*1024)
        lock = load_strict_json(here/'ANCESTOR_LOCK.json', 8*1024*1024)
        path_policy(manifest)
        identity = contract.check_merged_base(repo, lock)
        return {'schema': 'OPICA2_DESCENDANT_SOURCE_INSPECTION_V1', **identity,
                'status': 'PASS_SOURCE_SCOPE_ONLY', 'path_policy_sha256': AUDITED_PATH_POLICY,
                'round3_source_inspection': child,
                'source_lock_sha256': contract.digest(here/'ANCESTOR_LOCK.json'),
                'current_tree_compatibility_accepted': False, 'baseline_replay_accepted': False,
                'policy_review': 'EXPLICIT_PINNED_ROUND3_EXTENSION_SOURCE_SCOPE_ONLY',
                'full_core_accepted': False, 'full_release_accepted': False, 'RH': 'OPEN', 'Step4': 'OPEN'}
    manifest = load_strict_json(here/'BUILD_MANIFEST.json', 8*1024*1024)
    extension = load_strict_json(here/'DESCENDANT_EXTENSION.json', 8*1024*1024)
    lock = load_strict_json(here/'ANCESTOR_LOCK.json', 8*1024*1024)
    policy = path_policy(manifest)
    require(extension.get('schema') == 'OPICA2_DESCENDANT_EXTENSION_V1', 'Unknown extension version')
    require(extension.get('baseline') == contract.FROZEN_COMMIT
            and extension.get('baseline_tree') == contract.FROZEN_TREE, 'Frozen extension identity changed')
    require(sorted(extension.get('allowed_new_paths', [])) == policy['create']
            and sorted(extension.get('allowed_edit_paths', [])) == policy['edit'],
            'Extension and audited path inventories disagree')
    require(extension.get('manifest_sha256') == contract.digest(here/'BUILD_MANIFEST.json'),
            'Extension is not bound to the actual build manifest')
    identity = contract.check_merged_base(repo, lock)
    contract.check_source_lock(repo, lock['frozen_ancestor'], manifest)
    frozen_paths = {row['path'] for row in lock['frozen_ancestor']['source_manifest']}
    require(all(contract.file_at(repo, path).is_file() for path in frozen_paths),
            'An ancestor file was deleted')
    changed = contract.git(repo, 'diff', '--name-only', '--no-renames', contract.FROZEN_COMMIT).splitlines()
    untracked = contract.git(repo, 'ls-files', '--others', '--exclude-standard').splitlines()
    allowed_existing = set(policy['edit']) | set(policy['generated'])
    require(set(changed) <= allowed_existing | set(policy['create']), 'Unapproved tracked descendant path')
    require(set(untracked) <= set(policy['create']), 'Unapproved untracked descendant path')
    present_new = sorted(path for path in policy['create'] if contract.file_at(repo, path).is_file())
    return {'schema': 'OPICA2_DESCENDANT_SOURCE_INSPECTION_V1', **identity,
            'status': 'PASS_SOURCE_SCOPE_ONLY', 'path_policy_sha256': AUDITED_PATH_POLICY,
            'changed_existing_paths': sorted(set(changed) & allowed_existing),
            'present_new_paths': present_new, 'source_lock_sha256': contract.digest(here/'ANCESTOR_LOCK.json'),
            'current_tree_compatibility_accepted': False, 'baseline_replay_accepted': False,
            'policy_review': extension.get('policy_review', 'NOT_ESTABLISHED'),
            'full_core_accepted': False, 'full_release_accepted': False, 'RH': 'OPEN', 'Step4': 'OPEN'}


def verify_projection(path: Path, *, reference_repo: Path = REPO, here: Path = HERE) -> dict[str, Any]:
    path = path.resolve()
    require(path.is_dir() and not path.is_symlink(), 'Projection directory is missing or linked')
    require(contract.git(path, 'rev-parse', 'HEAD') == contract.FROZEN_COMMIT
            and contract.git(path, 'rev-parse', 'HEAD^{tree}') == contract.FROZEN_TREE,
            'Projection is not the frozen Git source identity')
    require(not contract.git(path, 'status', '--porcelain', '--untracked-files=all'),
            'Projection contains changed or untracked source')
    lock = load_strict_json(here/'ANCESTOR_LOCK.json', 8*1024*1024)
    require(contract.git(reference_repo, 'rev-parse', contract.FROZEN_COMMIT+'^{tree}') == contract.FROZEN_TREE,
            'Frozen reference is unavailable or changed')
    rows = lock['frozen_ancestor']['source_manifest']
    actual_index = contract.git(path, 'ls-tree', '-r', contract.FROZEN_COMMIT).splitlines()
    require(len(actual_index) == len(rows), 'Frozen projection path count differs')
    index = {line.split('\t', 1)[1]: tuple(line.split('\t', 1)[0].split()) for line in actual_index}
    require(set(index) == {row['path'] for row in rows}, 'Frozen projection path inventory differs')
    # Git status may hide globally ignored files. They cannot become silent
    # compiler providers in the frozen source projection.
    observed = set()
    for base, dirs, files in os.walk(path, followlinks=False):
        current = Path(base)
        if current == path:
            dirs[:] = [d for d in dirs if d not in ('.git','.lake')]
        for child in dirs:
            require(not (current/child).is_symlink(), 'Linked directory outside the declared compiler cache')
        for name in files:
            relative = (current/name).relative_to(path).as_posix()
            if relative != '.git':
                observed.add(relative)
    require(observed == set(index), 'Untracked or ignored source file in the frozen projection')
    for row in rows:
        require(index[row['path']] == (row['mode'], 'blob', row['git_blob']), 'Frozen mode/blob identity differs')
        source = contract.file_at(path, row['path'])
        require(source.is_file(), 'Frozen source file missing')
        size, blob, digest = contract.actual_blob_identity(source)
        require((size, blob, digest) == (row['bytes'], row['git_blob'], row['sha256']),
                'Frozen source bytes differ: '+row['path'])
    return {'schema': 'OPICA2_VERIFIED_ANCESTOR_PROJECTION_V1', 'path': str(path),
            'checked_commit': contract.FROZEN_COMMIT, 'checked_tree': contract.FROZEN_TREE,
            'source_files': len(rows), 'manifest_sha256': canonical_sha256(rows),
            'status': 'PASS_EXACT_FROZEN_SOURCE_ONLY', 'baseline_replay_accepted': False,
            'current_tree_compatibility_accepted': False, 'full_release_accepted': False}


def create_projection(repo: Path, destination: Path, *, here: Path = HERE) -> dict[str, Any]:
    repo, destination = repo.resolve(), destination.resolve()
    require(destination.is_relative_to(repo.parent) and destination != repo
            and not destination.is_relative_to(repo), 'Projection must be a private sibling checkout')
    require(not destination.exists(), 'Refusing to overwrite a projection or directory')
    inspection = inspect_descendant(repo, here)
    destination.parent.mkdir(parents=True, exist_ok=True)
    run = subprocess.run(['git', '-C', str(repo), 'worktree', 'add', '--detach', str(destination),
                          contract.FROZEN_COMMIT], capture_output=True, text=True, encoding='utf-8', timeout=180)
    require(run.returncode == 0, 'Creating the private frozen checkout failed: '+run.stderr[-2000:])
    result = verify_projection(destination, reference_repo=repo, here=here)
    result['descendant_source_inspection'] = inspection
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('inspect', 'create', 'verify'))
    parser.add_argument('--repo', type=Path, default=REPO)
    parser.add_argument('--destination', type=Path)
    args = parser.parse_args()
    try:
        if args.action == 'inspect':
            result = inspect_descendant(args.repo)
        else:
            require(args.destination is not None, '--destination is required')
            result = (create_projection(args.repo, args.destination) if args.action == 'create'
                      else verify_projection(args.destination, reference_repo=args.repo))
        print(json.dumps(result, indent=2))
        return 0
    except (InvalidCertificate, OSError, subprocess.SubprocessError, KeyError, ValueError) as exc:
        print(json.dumps(failure_envelope('ANCESTOR_PROJECTION_FAILED', str(exc)), indent=2))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
