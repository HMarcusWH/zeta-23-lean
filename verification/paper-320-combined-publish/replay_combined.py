"""Independently reproduce the combined review artifact. The output is diagnostic."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import zipfile

RUN = 46024089651
JOB = 140590858656
HELPER = '236001b317036a49aecb29d9a0d67e0565a6f27c'
BRANCH = 'workmode/paper-320-reviewed-generated-publish'
SOURCE = 'f3c45bf57d9d084f8337616978a3f15e4fa9df4d'
TREE = '1f5bc26c013592a9049b3e8eba2294dd710192a5'
MAIN = 'd4c7fc7114e5f1b61b90ea9037890969358ff0cc'
PAPER = '30b3a430c350eeeef9ff1aa8c99d10cd30dc3fb3'
REPO = 'HMarcusWH/zeta-23-lean'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def replay_delta(repo, reference, output, patch):
    for key in ('review_source','tree','parents','tracked','original_pdfs','independent_approval','canonical_admission','RH'):
        require(reference[key]==output[key], 'Output metadata changed: '+key)
    require((output['review_source'],output['tree'],output['parents'],output['tracked'])==(SOURCE,TREE,[MAIN,PAPER],5965),'Unexpected review source')
    require(reference['phase']=='before' and not reference['changed'] and output['phase']=='after','Wrong stages')
    old=reference['products'];new=output['products']
    require(len(old)==81 and set(old)==set(new) and sum(x['frozen'] for x in old.values())==4,'Product inventory mismatch')
    with tempfile.TemporaryDirectory() as td:
        env={**os.environ,'GIT_INDEX_FILE':str(Path(td)/'index'),'GIT_NO_REPLACE_OBJECTS':'1','GIT_NO_LAZY_FETCH':'1'}
        def git(*args,stdin=None):
            return subprocess.check_output(['git','-C',str(repo),*args],env=env,input=stdin)
        require(git('rev-parse',SOURCE+'^{tree}').decode().strip()==TREE,'Locally reconstructed source differs')
        git('read-tree',TREE)
        if patch:
            git('apply','--cached','--binary','--check','--whitespace=nowarn','-',stdin=patch)
            git('apply','--cached','--binary','--whitespace=nowarn','-',stdin=patch)
        tree=git('write-tree').decode().strip()
        changed=[x.decode() for x in git('diff','--name-only','-z',TREE,tree).split(b'\0') if x]
        require(sorted(changed)==sorted(output['changed']) and len(set(changed))==len(changed),'Claimed delta differs from the Git tree')
        require(set(changed)<={p for p,row in old.items() if not row['frozen']},'Patch changed a protected path')
        for p,row in new.items():
            require(row['input']==old[p]['input']==old[p]['output'] and row['frozen']==old[p]['frozen'],'Preimage or scope changed: '+p)
            info=git('ls-tree',tree,'--',p).decode().split('\t',1)[0].split()
            require(info==['100644','blob',row['output']],'Postimage or mode mismatch: '+p)
            require(digest(git('cat-file','blob',row['output']))==row['sha256'],'Postimage digest mismatch: '+p)
            if row['frozen']:
                require(row==old[p],'Frozen product changed: '+p)
        return {'source':SOURCE,'source_tree':TREE,'replayed_tree':tree,'canonical_patch_sha256':digest(patch),'changed':changed,
                'permitted_products':77,'frozen_products':4,'original_pdfs':6,'source_approval':False,'canonical_admission':False,'RH':'OPEN'}

def authenticate(repo, folder):
    read=lambda n:json.loads((folder/n).read_bytes())
    run=read('run.json');art=read('artifact.json');job=read('job.json')
    require((run['id'],run['run_attempt'],run['head_sha'],run['head_branch'],run['repository']['full_name'],run['status'],run['conclusion'])==(RUN,1,HELPER,BRANCH,REPO,'completed','success'),'Exact helper job has not passed')
    require((job['id'],job['run_id'],job['status'],job['conclusion'])==(JOB,RUN,'completed','success'),'Wrong job')
    required={'Reproduce exact parents and their independent original checks','Materialize and check the review candidate with the original exporters'}
    require(required<={s['name'] for s in job['steps'] if s['conclusion']=='success'},'Required CI steps failed')
    require((art['name'],art['expired'],art['workflow_run']['id'],art['workflow_run']['head_sha'])==
            (f'paper-main-review-only-{RUN}-1',False,RUN,HELPER),'Wrong artifact origin')
    archive=folder/'artifact.zip'
    with archive.open('rb') as f: require('sha256:'+hashlib.file_digest(f,'sha256').hexdigest()==art['digest'] and archive.stat().st_size==art['size_in_bytes'],'Artifact ZIP mismatch')
    with zipfile.ZipFile(archive) as z:
        require(len(z.namelist())==len(set(z.namelist())),'Duplicate member')
        hashes={name:h for h,name in (s.split() for s in z.read('hashes.txt').decode().splitlines())}
        require(set(hashes)=={'candidate-products.patch','input.json','output.json'},'Hash manifest differs')
        for n,h in hashes.items():require(digest(z.read(n))==h,n)
        for n,head,schema in [('main-source.json',MAIN,'OPICA_DISPATCH_REGISTRATION_INSPECTION_V1'),('paper-source.json',PAPER,'RHRC_PAPER_DOCUMENTATION_SOURCE_INSPECTION_V1')]:
            row=json.loads(z.read(n));require((row['checked_commit'],row['schema'],row['status'],row['RH'])==(head,schema,'PASS_SOURCE_SCOPE_ONLY','OPEN'),n)
            want=subprocess.check_output(['git','-C',str(repo),'rev-parse',head+'^{tree}']).decode().strip()
            require(row['checked_tree']==want,'Parent validator observed wrong tree')
        local=json.loads(Path(__file__).with_name('local-inputs.json').read_bytes())
        require(json.loads(z.read('input.json'))==local,'Hosted input census differs from independent local reconstruction')
        result=replay_delta(repo,local,json.loads(z.read('output.json')),z.read('candidate-products.patch'))
    result.update(run=RUN,job=JOB,artifact=art['id'],archive_sha256=art['digest'])
    (folder/'authenticated-candidate.json').write_text(json.dumps(result,indent=2)+'\n')
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('repo',type=Path);p.add_argument('folder',type=Path)
    args=p.parse_args();print(json.dumps(authenticate(args.repo,args.folder),indent=2))
