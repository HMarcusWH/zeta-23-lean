"""Capture source identity before child edits. Source capture is not release acceptance."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PINNED_HEAD = '553b4263b58d9fec178320de251ff299a0bd702a'
ACCEPTED_PARENT = 'd53dd70d38b0762af130b1d19b795af259f505f5'
PINNED_TREE = '12691099f1a155a8bfa3ad4f6689146175b233b2'


def git(*args: str) -> bytes:
    return subprocess.run(['git', '-C', str(REPO), *args], check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def capture(expected_head: str, expected_tree: str) -> dict:
    if expected_head not in {PINNED_HEAD, ACCEPTED_PARENT} or expected_tree != PINNED_TREE:
        raise ValueError('unreviewed parent pin; a versioned amendment is required')
    if git('rev-parse', expected_head + '^{tree}').decode().strip() != expected_tree:
        raise ValueError('parent commit/tree mismatch')
    if git('rev-parse', 'HEAD').decode().strip() != expected_head:
        raise ValueError('source capture requires the exact parent HEAD')
    # Untracked child work is excluded from this frozen parent inventory. Every
    # tracked parent's working bytes must still match its committed blob.
    if git('diff', '--name-only', 'HEAD', '--'):
        raise ValueError('tracked parent edits already present')
    rows = []
    for entry in git('ls-tree', '-r', '-z', expected_head).split(b'\0'):
        if not entry:
            continue
        meta, raw_path = entry.split(b'\t', 1)
        mode, kind, oid = meta.decode().split()
        path = raw_path.decode('utf-8')
        if kind != 'blob' or mode not in {'100644', '100755'}:
            raise ValueError('unsupported parent tree entry: ' + path)
        target = REPO / path
        if target.is_symlink() or not target.resolve().is_relative_to(REPO.resolve()):
            raise ValueError('parent path escapes checkout: ' + path)
        content = target.read_bytes()
        # Git blob identity checks exact bytes; no line-ending conversion.
        actual_blob = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        if actual_blob != oid:
            raise ValueError('working bytes differ from parent blob: ' + path)
        rows.append({'path': path, 'mode': mode, 'git_blob': oid,
                     'bytes': len(content), 'sha256': hashlib.sha256(content).hexdigest()})
    def read(relative):
        return json.loads((REPO / relative).read_text(encoding='utf-8'))
    claims = read('research/RHRC/CLAIM_REGISTRY.json')
    bindings = read('research/RHRC/REGISTERED_THEOREM_BINDINGS.json')
    open_ids = ['C_RH', 'R001_PRIME_UPPER', 'R002_WINDOWED_VISIBILITY',
                'R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES']
    return {'schema': 'OPICA_FOLLOWUP_PROTECTED_PARENT_V1', 'parent_head': expected_head,
            'original_pr_head': PINNED_HEAD, 'parent_tree': expected_tree,
            'phase': 'SOURCE_CAPTURE_ONLY', 'compiler_validated_here': False,
            'review_status': 'INDEPENDENT_REVIEW_NOT_ESTABLISHED',
            'files': rows, 'claim_registry': claims, 'theorem_bindings': bindings,
            'file_classes': read('research/RHRC/graph/FILE_CLASSES.json'),
            'semantic_closure': read('research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json'),
            'open_claim_ids': open_ids, 'RH': 'OPEN', 'Step4': 'OPEN'}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent-pr', type=int, required=True)
    parser.add_argument('--expected-head', required=True)
    parser.add_argument('--expected-tree', required=True)
    parser.add_argument('--phase', choices=['source', 'acceptance'], required=True)
    parser.add_argument('--formal-receipt', type=Path)
    parser.add_argument('--workflow-harvest', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.parent_pr != 293:
        parser.error('only parent PR293 is authorized')
    if args.phase == 'acceptance':
        # A source hash or a successful generic JSON receipt cannot establish
        # acceptance. Full parent receipt verification is a later milestone.
        parser.error('acceptance is closed until exact P0 receipt verification is implemented')
    report = capture(args.expected_head, args.expected_tree)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': report['phase'], 'parent_head': report['parent_head'],
                      'parent_tree': report['parent_tree'], 'tracked_files': len(report['files']),
                      'claims': len(report['claim_registry']['claims']),
                      'bindings': len(report['theorem_bindings']['bindings']),
                      'release_acceptance': False}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
