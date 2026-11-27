"""Inspect the actual two-parent source and bind canonical output to its complete input."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

MAIN = 'd4c7fc7114e5f1b61b90ea9037890969358ff0cc'
PAPER = '30b3a430c350eeeef9ff1aa8c99d10cd30dc3fb3'
TREE = '1f5bc26c013592a9049b3e8eba2294dd710192a5'
DRAFT = 'f3c45bf57d9d084f8337616978a3f15e4fa9df4d'
MANIFEST = 'research/RHRC/integration/opica_round4/BUILD_MANIFEST.json'
PAPER_POLICY = 'research/RHRC/integration/documentation_2026_11_21/SOURCE_SCOPE.json'
ARCHIVE = 'research/RHRC/integration/documentation_2026_11_26/ARCHIVE_BYTES.json'

def require(ok, msg):
    if not ok:
        raise ValueError(msg)

def inspect(repo, phase):
    env={**os.environ,'GIT_NO_REPLACE_OBJECTS':'1','GIT_OPTIONAL_LOCKS':'0'}
    def git(*args,stdin=None):
        return subprocess.check_output(['git','-C',str(repo),*args],input=stdin,env=env)
    require(git('rev-parse','HEAD','HEAD^{tree}','HEAD^1','HEAD^2').decode().splitlines()==[DRAFT,TREE,MAIN,PAPER],'Draft ancestry or tree differs')
    require(len(git('show','-s','--format=%P','HEAD').split())==2,'Exactly two parents required')
    allowed=set(json.loads(git('show',PAPER+':'+PAPER_POLICY))['generated'])
    records=json.loads(git('show',PAPER+':'+MANIFEST))['generated']
    products={r['path'] for r in records}
    frozen=products-allowed
    require(len(records)==len(products)==81 and len(allowed)==77 and len(frozen)==4 and allowed<=products,'81 product boundary')
    pdfs={p:r for p,r in json.loads(git('show',PAPER+':'+ARCHIVE))['added'].items() if r['file_kind']=='BINARY_PDF'}
    require(len(pdfs)==6,'PDF count')
    for p,r in pdfs.items():
        data=(repo/p).read_bytes()
        require(len(data)==r['size_bytes'] and hashlib.sha256(data).hexdigest()==r['sha256'],'PDF changed: '+p)
    require(not git('ls-files','--others','--exclude-standard','-z'),'Untracked source')
    require(not git('diff','--cached','--name-only','-z'),'Staged mutation')
    expected={}
    for raw in git('ls-tree','-r','-z','HEAD').split(b'\0'):
        if raw:
            head,p=raw.split(b'\t',1)
            mode,kind,oid=head.decode().split();name=p.decode()
            require(kind=='blob' and mode in {'100644','100755'},'Original path mode '+name)
            expected[name]=(mode,oid)
    require(len(expected)==5965,'Complete input census')
    paths=sorted(expected)
    actual=git('hash-object','--no-filters','--stdin-paths',stdin=('\n'.join(paths)+'\n').encode()).decode().splitlines()
    require(len(actual)==len(paths),'Truncated input')
    changed=[]
    rows={}
    for p,oid in zip(paths,actual,strict=True):
        f=repo/p;mode,old=expected[p]
        require(not f.is_symlink() and f.is_file() and bool(f.stat().st_mode&0o100)==(mode=='100755'),'Unexpected file mode '+p)
        if old!=oid:
            require(phase=='after' and p in allowed,'Unexpected checked-out byte change '+p)
            changed.append(p)
        if p in products:
            rows[p]={'input':old,'output':oid,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'frozen':p in frozen}
    require(all(rows[p]['input']==rows[p]['output'] for p in frozen),'Frozen product drift')
    return {'phase':phase,'review_source':DRAFT,'tree':TREE,'parents':[MAIN,PAPER],
            'tracked':len(paths),'products':rows,'changed':changed,'original_pdfs':sorted(pdfs),
            'independent_approval':False,'canonical_admission':False,'RH':'OPEN'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('repo',type=Path);p.add_argument('phase',choices=['before','after']);p.add_argument('output',type=Path)
    a=p.parse_args(); a.output.write_text(json.dumps(inspect(a.repo.resolve(),a.phase),indent=2)+'\n')
