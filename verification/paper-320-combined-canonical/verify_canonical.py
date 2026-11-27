"""Authenticate the original documentation producer and reconstruct its combined-epoch Git tree without moving refs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile
import zipfile

REPOSITORY = 'HMarcusWH/zeta-23-lean'
REPOSITORY_ID = 1339954300
BRANCH = 'review/paper-320-combined-source'
REGISTRATION = 'd4c7fc7114e5f1b61b90ea9037890969358ff0cc'
PAPER = '30b3a430c350eeeef9ff1aa8c99d10cd30dc3fb3'
ARCHIVE = '59ff631e9e965abdb172c941b8dacee44eb97629'
LAYOUT = 'f3c45bf57d9d084f8337616978a3f15e4fa9df4d'
SEED = '0242ac003843a5d9bf612d72491d23189e319203'
ROOT = 'research/RHRC/integration/'
INVENTORY = 'research/RHRC/graph/generated/repository_files.jsonl'
CANONICAL_STEPS = {'Authenticate source and build the existing exporters',
                   'Regenerate through the canonical producer and check its output'}
MEMBERS = {'input-head-tree.txt', 'source-scope.json', 'lean-version.txt', 'exporter-build.log',
           'materialize.log', 'canonical-check.log', 'generated-state.patch', 'generated-stat.txt',
           'generated-state.patch.sha256'}

def require(value, message):
    if not value:
        raise ValueError(message)

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def git(repo, *args, data=None, env=None):
    return subprocess.check_output(['git', '-C', str(repo), *args], input=data,
                                  env={**os.environ, 'GIT_NO_REPLACE_OBJECTS': '1',
                                       'GIT_NO_LAZY_FETCH': '1', **(env or {})})

def inventory(repo, tree):
    result = {}
    for record in git(repo, 'ls-tree', '-rz', tree).split(b'\0'):
        if record:
            info, path = record.decode().split('\t', 1)
            result[path] = tuple(info.split())
    return result

def read_policy(repo, name):
    return json.loads(git(repo, 'show', PAPER + ':' + ROOT + name))

def check_lineage(repo, head, tree):
    require(re.fullmatch('[0-9a-f]{40}', head) and re.fullmatch('[0-9a-f]{40}', tree), 'Full SHA required')
    require(git(repo, 'show', '-s', '--format=%T %P', LAYOUT).decode().split() ==
            ['1f5bc26c013592a9049b3e8eba2294dd710192a5', REGISTRATION, PAPER], 'Source-parent layout differs')
    require(git(repo, 'show', '-s', '--format=%T %P', SEED).decode().split() ==
            ['dd10422dc0b48b5e3494823910464a10048edc94', LAYOUT], 'Product seed differs')
    git(repo, 'merge-base', '--is-ancestor', ARCHIVE, PAPER)
    git(repo, 'merge-base', '--is-ancestor', SEED, head)
    require(git(repo, 'rev-parse', head+'^{tree}').decode().strip() == tree, 'Source tree differs')

def check_graph(repo, after, allowed, pdfs):
    rows = {}
    paper_rows = set()
    for line in git(repo, 'cat-file', 'blob', after[INVENTORY][2]).splitlines():
        row = json.loads(line)
        path = row['path']
        require(path not in rows and path in after and row['type'] == 'RepoFile', 'Unexpected graph row: ' + path)
        rows[path] = True
        loc = row['source_locator']
        require((loc['path'], loc['repository']) == (path, REPOSITORY), 'Wrong graph locator: ' + path)
        if path in allowed:
            require(row['generated_product'] is True and row['git_blob'] is None and
                    loc.get('generated_product') is True and 'blob_sha' not in loc, 'Bad generated row: ' + path)
        else:
            require(row['generated_product'] is False and row['git_blob'] == loc['blob_sha'] == after[path][2],
                    'Stale source row: ' + path)
        if row['classification_rule'] == 'research_archive_2026_11_26_papers':
            require((row['file_class'], row['trust_zone']) == ('RESEARCH_FIXTURE', 'AUDIT_ONLY'),
                    'Changed paper classification: ' + path)
            paper_rows.add(path)
    require(set(rows) == set(after) and paper_rows == set(pdfs), 'Graph coverage or archived paper scope differs')

def replay_delta(repo, head, tree, patch):
    require(git(repo, 'rev-parse', head+'^{tree}').decode().strip() == tree, 'Source SHA/tree mismatch')
    active = set(read_policy(repo, 'documentation_2026_11_21/SOURCE_SCOPE.json')['generated'])
    all_products = {row['path'] for row in read_policy(repo, 'opica_round4/BUILD_MANIFEST.json')['generated']}
    frozen = all_products - active
    require(len(all_products) == 81 and active <= all_products and len(frozen) == 4, 'Original scope differs')
    pdfs = {p: row for p, row in read_policy(repo, 'documentation_2026_11_26/ARCHIVE_BYTES.json')['added'].items()
            if row['file_kind'] == 'BINARY_PDF'}
    require(len(pdfs) == 6, 'Original PDF census differs')
    before = inventory(repo, tree)
    archived = inventory(repo, PAPER)
    with tempfile.TemporaryDirectory() as temp:
        env = {'GIT_INDEX_FILE': str(Path(temp)/'index')}
        git(repo, 'read-tree', tree, env=env)
        if patch:
            git(repo, 'apply', '--cached', '--binary', '--check', '--whitespace=nowarn', '-', data=patch, env=env)
            git(repo, 'apply', '--cached', '--binary', '--whitespace=nowarn', '-', data=patch, env=env)
        candidate = git(repo, 'write-tree', env=env).decode().strip()
        git(repo, 'diff', '--check', tree, candidate, env=env)
    after = inventory(repo, candidate)
    require(before.keys() == after.keys(), 'Tracked path set changed')
    changed = sorted(p for p in before if before[p] != after[p])
    require(set(changed) <= active, 'Generated patch contains protected source changes')
    census = {}
    for path in sorted(all_products):
        old_mode, old_kind, old = before[path]
        mode, kind, new = after[path]
        require((old_mode, old_kind, mode, kind) == ('100644','blob','100644','blob'), 'Nonregular product: ' + path)
        if path in frozen:
            require(before[path] == after[path] == archived[path], 'Historical product changed: ' + path)
        preimage = git(repo, 'cat-file', 'blob', old)
        postimage = preimage if old == new else git(repo, 'cat-file', 'blob', new)
        census[path] = {'frozen': path in frozen, 'preimage': old, 'preimage_sha256': sha256(preimage),
                        'postimage': new, 'postimage_sha256': sha256(postimage), 'postimage_bytes': len(postimage)}
    for path, expected in pdfs.items():
        require(before[path] == after[path] == archived[path] == ('100644', 'blob', expected['git_blob']),
                'Paper blob or mode changed: ' + path)
        data = git(repo, 'cat-file', 'blob', expected['git_blob'])
        require((sha256(data), len(data)) == (expected['sha256'], expected['size_bytes']), 'Paper bytes changed: ' + path)
    check_graph(repo, after, active, pdfs)
    return {'source': head, 'source_tree':tree, 'candidate_tree': candidate, 'patch_sha256': sha256(patch),
            'changed': changed, 'tracked':len(after), 'products':census, 'pdfs':pdfs,
            'allowed_products':len(active), 'frozen_products':len(frozen), 'RH':'OPEN', 'Step4':'OPEN'}

def authenticate_documentation(repo, folder, head, tree, run_id, attempt):
    job=json.loads((folder/'documentation-job.json').read_bytes())
    art=json.loads((folder/'documentation-artifact.json').read_bytes())
    require((job['run_id'],job['run_attempt'],job['head_sha'],job['head_branch'],job['status'],job['conclusion'],job['name']) ==
            (run_id,attempt,head,BRANCH,'completed','success','documentation'), 'Source and examples job differs')
    names={s['name'] for s in job['steps'] if s['conclusion']=='success'}
    require({'Check the exact archive and documentation source boundary','Check reader links and run bounded exact examples'} <= names,
            'Historical, mixed scope or reader checks did not pass')
    origin=art['workflow_run']
    require((origin['id'],origin['head_sha'],origin['head_branch'],origin['repository_id'],origin['head_repository_id'],
             art['name'],art['expired']) ==
            (run_id,head,BRANCH,REPOSITORY_ID,REPOSITORY_ID,f'documentation-{run_id}-{attempt}',False),
            'Incorrect original source-scope artifact')
    archive=folder/'documentation.zip'
    with archive.open('rb') as f:
        require(archive.stat().st_size==art['size_in_bytes'] and
                'sha256:'+hashlib.file_digest(f,'sha256').hexdigest()==art['digest'], 'Source artifact digest differs')
    with zipfile.ZipFile(archive) as z:
        require(len(z.infolist())==len(set(z.namelist())), 'Duplicate source artifact member')
        require(z.read('head-tree.txt').decode().splitlines()==[head,tree], 'Source job checkout differs')
        for member,sha,schema in [('registration-parent.json',REGISTRATION,'OPICA_DISPATCH_REGISTRATION_INSPECTION_V1'),
                                  ('paper-parent.json',PAPER,'RHRC_PAPER_DOCUMENTATION_SOURCE_INSPECTION_V1'),
                                  ('combined-source.json',head,'RHRC_COMBINED_DOCUMENTATION_SOURCE_INSPECTION_V1')]:
            rr=json.loads(z.read(member))
            require((rr['schema'],rr['status'],rr['checked_commit'],rr['checked_tree'],rr['RH'],rr['Step4']) ==
                    (schema,'PASS_SOURCE_SCOPE_ONLY',sha,git(repo,'rev-parse',sha+'^{tree}').decode().strip(),'OPEN','OPEN'),
                    'Wrong exact parent or mixed source scope receipt: '+member)
        for name in ('paper-tests.log','paper-tests-optimized.log','combined-tests.log','combined-tests-optimized.log'):
            require(z.read(name).rstrip().endswith(b'OK'), 'Missing original normal/optimized tests: '+name)
        require(json.loads(z.read('registration-classes.json'))['status']=='PASS_REGISTRATION_CLASSIFICATION_ONLY' and
                b'PASS_AUDIT_ONLY' in z.read('combined-classes.log'), 'Incorrect parent or combined classification')
        receipt=json.loads(z.read('combined-source.json'))
    return {'job':job['id'],'artifact':art['id'],'sha256':art['digest'],'combined_scope':receipt}

def authenticate(repo, folder, head, tree, run_id, attempt, job_id, artifact_id, digest):
    check_lineage(repo, head, tree)
    source_docs=authenticate_documentation(repo,folder,head,tree,run_id,attempt)
    run, job, art = (json.loads((folder/(name+'.json')).read_bytes()) for name in ('run','job','artifact'))
    require((run['id'], run['run_attempt'], run['head_sha'], run['head_branch'], run['event'], run['workflow_id'],
             run['path'], run['status'], run['conclusion']) ==
            (run_id, attempt, head, BRANCH, 'workflow_dispatch', 425927168, '.github/workflows/documentation.yml',
             'completed', 'success'), 'Wrong, incomplete or failed original workflow')
    for field in ('repository','head_repository'):
        require((run[field]['id'], run[field]['full_name']) == (REPOSITORY_ID, REPOSITORY), 'Workflow repository differs')
    require((job['id'], job['run_id'], job['run_attempt'], job['name'], job['status'], job['conclusion']) ==
            (job_id, run_id, attempt, 'Canonical generated-state candidate for documentation', 'completed', 'success'),
            'Wrong canonical job or attempt')
    require((job['head_sha'],job['head_branch']) == (head,BRANCH), 'Job head differs')
    require(CANONICAL_STEPS <= {x['name'] for x in job['steps'] if x['conclusion']=='success'}, 'Missing exporter or producer step')
    origin = art['workflow_run']
    require((origin['id'], origin['head_sha'], origin['head_branch'], origin['repository_id'], origin['head_repository_id']) ==
            (run_id, head, BRANCH, REPOSITORY_ID, REPOSITORY_ID), 'Artifact source differs')
    require(re.fullmatch('[0-9a-f]{64}', digest) and
            (art['id'], art['name'], art['digest'], art['expired']) ==
            (artifact_id, f'documentation-canonical-{run_id}-{attempt}', 'sha256:'+digest, False), 'Artifact identity differs')
    archive = folder/'artifact.zip'
    with archive.open('rb') as f:
        require(archive.stat().st_size == art['size_in_bytes'] and hashlib.file_digest(f, 'sha256').hexdigest() == digest,
                'Archive size or digest mismatch')
    with zipfile.ZipFile(archive) as z:
        require(len(z.infolist()) == len(MEMBERS) and set(z.namelist()) == MEMBERS, 'Archive member inventory mismatch')
        require(all(stat.S_IFMT(i.external_attr>>16) in (0, stat.S_IFREG) and not i.is_dir() for i in z.infolist()),
                'Nonregular archive member')
        require(z.read('input-head-tree.txt').decode().splitlines() == [head,tree], 'Producer checkout differs')
        scope = json.loads(z.read('source-scope.json'))
        require(scope == source_docs.pop('combined_scope'), 'Two original jobs disagree on the exact source')
        require((scope['schema'],scope['status'],scope['checked_commit'],scope['checked_tree'],scope['RH'],scope['Step4']) ==
                ('RHRC_COMBINED_DOCUMENTATION_SOURCE_INSPECTION_V1','PASS_SOURCE_SCOPE_ONLY',head,tree,'OPEN','OPEN'),
                'Mixed-epoch source scope receipt differs')
        require((scope['base'],scope['base_tree'],scope['layout'],scope['source_parents'],scope['canonical_product_count'],
                 scope['unchanged_historical_product_count']) ==
                (SEED,'dd10422dc0b48b5e3494823910464a10048edc94',LAYOUT,[REGISTRATION,PAPER],77,4),
                'Combined lineage and inventory differ')
        require(scope['path_policy'] == sha256(git(repo,'show',head+':'+ROOT+'documentation_combined/SOURCE_SCOPE.json')) and
                scope['paper_archive']['archive_commit'] == ARCHIVE and scope['paper_archive']['article_pdf_count'] == 6 and
                all(scope[k] is False for k in ('canonical_admission','independent_approval','proof_acceptance',
                                                'current_compiler_accepted','full_round4_accepted')),
                'Source policy digest, archive or acceptance boundary differs')
        require(z.read('materialize.log').rstrip().endswith(b'RHRC DERIVED STATE: MATERIALIZED') and
                z.read('canonical-check.log').rstrip().endswith(b'RHRC DERIVED STATE: PASS'), 'Original producer markers missing')
        toolchain = git(repo, 'show', head+':lean-toolchain').decode().strip().split(':')[-1].lstrip('v')
        require(z.read('lean-version.txt').startswith(('Lean (version '+toolchain+',').encode()), 'Compiler version differs')
        require(b'Build completed successfully' in z.read('exporter-build.log'), 'No completed original exporter build')
        patch = z.read('generated-state.patch')
        require(z.read('generated-state.patch.sha256').decode().split() == [sha256(patch),'generated-state.patch'],
                'Patch digest mismatch')
        receipt = replay_delta(repo, head, tree, patch)
    receipt.update(run=run_id, attempt=attempt, job=job_id, artifact=artifact_id, archive_sha256=digest,
                   source_verification=source_docs, combined_source_scope=scope['schema'], canonical_admission=False, independent_semantic_approval=False)
    return receipt

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['repo','folder','out']:
        p.add_argument('--'+arg, type=Path, required=True)
    for arg in ['head','tree','sha256']:
        p.add_argument('--'+arg, required=True)
    for arg in ['run','attempt','job','artifact']:
        p.add_argument('--'+arg, type=int, required=True)
    a=p.parse_args()
    result=authenticate(a.repo, a.folder, a.head, a.tree, a.run, a.attempt, a.job, a.artifact, a.sha256)
    a.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('source','candidate_tree','run','job','artifact','changed','tracked')}))
