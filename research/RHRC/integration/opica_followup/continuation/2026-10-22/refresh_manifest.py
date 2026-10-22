"""Refresh this explicit draft-artifact inventory and its preparation-validator pin.

Run after reviewing artifact changes. This does not update theorem acceptance,
the frozen specification, parent permissions or the full release gate.
"""
from pathlib import Path
import hashlib
import json
import re
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
CONTRACT = HERE.parents[1]


def main():
    artifacts = [REPO/'AGENTS.md']
    sys.path.insert(0, str(CONTRACT))
    from validate_contract import CONTINUATION_DOCUMENTATION_PATHS
    refinement = json.loads((HERE/'provenance/DOC_NAVIGATION_AMENDMENT.json').read_bytes())
    if set(refinement['additional_exact_documentation_paths']) != CONTINUATION_DOCUMENTATION_PATHS:
        raise ValueError('Documentation amendment differs from exact validator allowlist')
    artifacts += [REPO/path for path in sorted(CONTINUATION_DOCUMENTATION_PATHS)]
    for path in HERE.rglob('*'):
        if path.is_symlink():
            raise ValueError('Symlink in checkpoint: '+str(path))
        if path.is_file() and '__pycache__' not in path.parts and path.suffix != '.pyc':
            artifacts.append(path)
    rows = [{'path': p.relative_to(REPO).as_posix(), 'bytes': p.stat().st_size,
             'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in artifacts]
    rows.sort(key=lambda r: r['path'])
    manifest = {
        'schema': 'OPICA_CONTINUATION_CHECKPOINT_V1', 'id': 'CP_2026_10_22_01',
        'date': '2026-10-22', 'status': 'DRAFT_NO_FULL_ACCEPTANCE',
        'base_commit': '9b6a9a3a2badb4cff62a56c1158d9cef8759d30d',
        'parent_commit': 'd53dd70d38b0762af130b1d19b795af259f505f5',
        'original_primary_roots': 100, 'acceptance_units': 28,
        'frozen_public_roots_sha256': '2239636f347449ecd447fc5ba78d7c75f1c0440d28a862cb72397c4f79597b41',
        'release_ready': False, 'RH': 'OPEN', 'Step4': 'OPEN',
        'independent_closing_inequalities': 'OPEN',
        'new_mandatory_roots': [], 'frozen_statement_changes': [],
        'parent_mathematical_source_changes': [],
        'authority': 'EXACT_DRAFT_ARTIFACT_INVENTORY_ONLY_NOT_COMPILER_OR_RELEASE_EVIDENCE',
        'documentation_navigation_amendment': 'DOC_NAV_2026_10_22_01',
        'additional_documentation_paths': sorted(CONTINUATION_DOCUMENTATION_PATHS),
        'scope_note': 'The original84-file plan is frozen. These additional audited handover/input/evidence paths are an explicit checkpoint refinement. Full-extension/canonical reconciliation remains OPEN.',
        'artifacts': rows,
    }
    payload = (json.dumps(manifest, indent=2, ensure_ascii=False)+'\n').encode('utf-8')
    (CONTRACT/'CONTINUATION_MANIFEST.json').write_bytes(payload)
    digest = hashlib.sha256(payload).hexdigest()
    validator = CONTRACT/'validate_contract.py'
    data = validator.read_bytes()
    replacement = ("CONTINUATION_MANIFEST_SHA256 = '"+digest+"'").encode('ascii')
    updated, count = re.subn(rb'^CONTINUATION_MANIFEST_SHA256 = [^\r\n]*', replacement, data, flags=re.M)
    if count != 1:
        raise ValueError('Expected exactly one checkpoint pin')
    validator.write_bytes(updated)
    print(json.dumps({'artifacts': len(rows), 'manifest_sha256': digest,
                      'proof_or_release_authority': False}, indent=2))


if __name__ == '__main__':
    main()
