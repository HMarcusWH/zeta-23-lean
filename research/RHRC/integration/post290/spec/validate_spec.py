#!/usr/bin/env python3
"""Validate this specification bundle, not a Lean implementation or an RH claim."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys
import zipfile

def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    root = args.bundle.resolve()
    try:
        manifest = json.loads((root/'BUILD_MANIFEST.json').read_text())
        sources = json.loads((root/'SOURCE_REGISTER.json').read_text())
        hashes = json.loads((root/'MANIFEST_SHA256.json').read_text())
        modules = manifest['new_lean_modules']
        by_id = {m['id']: m for m in modules}
        if len(by_id) != len(modules):
            raise ValueError('Duplicate module IDs')
        if len({m['path'] for m in modules}) != len(modules):
            raise ValueError('Duplicate proposed module paths')
        done: set[str] = set()
        visiting: set[str] = set()
        def visit(mid: str) -> None:
            if mid in done:
                return
            if mid in visiting or mid not in by_id:
                raise ValueError(f'Cyclic or unresolved dependency: {mid}')
            visiting.add(mid)
            for dep in by_id[mid]['depends_on']:
                visit(dep)
            visiting.remove(mid)
            done.add(mid)
        for mid in by_id:
            visit(mid)
        for name, expected in hashes['files'].items():
            target = (root/name).resolve()
            if root not in target.parents:
                raise ValueError(f'Unsafe manifest path: {name}')
            if digest(target) != expected:
                raise ValueError(f'Hash mismatch: {name}')
        for item in sources['inputs']:
            target = root/item['path']
            if digest(target) != item['sha256']:
                raise ValueError(f'Source mismatch: {item["path"]}')
            with zipfile.ZipFile(target) as archive:
                bad = archive.testzip()
                if bad:
                    raise ValueError(f'Corrupt source archive member: {bad}')
        if manifest['status'] != 'PROPOSED_NOT_IMPLEMENTED' or manifest['claim_cap'] != 'RH_OPEN':
            raise ValueError('Specification status/claim cap changed')
        if not manifest['d2']['mandatory'] or not manifest['d2']['final_nonpartial_check_required']:
            raise ValueError('D2 requirement weakened')
        print(json.dumps({'result':'SPEC_BUNDLE_VALID','proposed_modules':len(modules),'verified_file_hashes':len(hashes['files']),'source_archives':len(sources['inputs']),'claim_cap':'RH_OPEN','scope':'Packaging and dependency specifications only; no theorem, numerical or implementation validation.'}, indent=2))
        return 0
    except (OSError, ValueError, KeyError, json.JSONDecodeError, zipfile.BadZipFile) as exc:
        print(f'SPEC_BUNDLE_INVALID: {exc}', file=sys.stderr)
        return 1

if __name__ == '__main__':
    raise SystemExit(main())
