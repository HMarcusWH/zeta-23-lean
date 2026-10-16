"""Verify the immutable specification and pinned source bytes, not theorem truth."""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[5]
INTEGRATION = REPO / 'research/RHRC/integration/post290'

def check():
    spec = INTEGRATION / 'spec'
    register = json.loads((spec / 'SOURCE_REGISTER.json').read_text())
    base, tree = register['base_commit'], register['base_tree']
    git = lambda *args: subprocess.check_output(['git', *args], cwd=REPO)
    if git('rev-parse', base + '^{tree}').decode().strip() != tree:
        raise ValueError('pinned baseline tree mismatch')
    sources = []
    for row in register['repository_sources']:
        raw = git('show', base + ':' + row['path'])
        digest = hashlib.sha256(raw).hexdigest()
        blob = git('rev-parse', base + ':' + row['path']).decode().strip()
        if digest != row['sha256'] or blob != row['git_blob']:
            raise ValueError('canonical source mismatch: ' + row['path'])
        sources.append({'path': row['path'], 'sha256': digest, 'git_blob': blob})
    archives = []
    for row in register['inputs']:
        path = spec / row['path']
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != row['sha256']:
            raise ValueError('paper archive mismatch: ' + row['path'])
        archives.append({'path': row['path'], 'sha256': digest})
    return {'execution_status': 'SUCCESS', 'integrity_status': 'PASS',
            'scientific_disposition': 'SOURCE_BYTES_PRESERVED', 'claim_cap': 'RH_OPEN',
            'formal_authority': 'NONE_CREATED', 'base_commit': base, 'base_tree': tree,
            'repository_sources': sources, 'paper_archives': archives,
            'scope': 'Canonical Git blobs at the historical base and unchanged paper ZIP bytes; no mathematical proof.'}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path)
    args = p.parse_args()
    result = check()
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('repository_sources','paper_archives')}))
