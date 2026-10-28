"""Fresh selected Permansson compilation in its separate pinned Lean4.34 world.

This runner never downloads dependencies or changes pins. Its final verifier
rebuilds the selected source closure and independent consumers; producer JSON
or registry labels alone cannot admit provider capability.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path,PurePosixPath,PureWindowsPath
import re
import shutil
import stat
import subprocess
import sys
import time
from .canonical import require,load_bytes,canonical_bytes,digest,ContractError
from .snapshot import unlinked,file_hash,git
from research.RHRC.permansson.opica_composition import (
    PROVIDER_COMMIT,PROVIDER_LEAN,PROVIDER_REPO,SELECTED_APIS,qualify_provider)

HERE=Path(__file__).resolve().parent
HOST=HERE.parents[3]
CONFIG=HERE/'providers/permansson/selected_exports.json'
TEMPLATE=HERE/'providers/permansson/ProviderAudit.lean.in'
MODULE='PermanssonResearch.ReverseSolver.ComputableFiniteMonitor'
MARKER='OPICA_PROVIDER\t'
MODULE_MARKER='OPICA_PROVIDER_MODULES\t'
ALLOWED={'propext','Classical.choice','Quot.sound'}
IMPORT=re.compile(r'^import ([A-Za-z_][A-Za-z0-9_.]*)',re.M)
CHECKOUT_EOL='true' if os.name=='nt' else 'false'


class BatchHasher:
    """Exact bytes; vet each trusted directory once during one source pass.

    Files are rechecked on every read. Provider/package roots are evaluator-owned;
    independent before/after passes still rehash all bytes and recheck directories.
    """
    def __init__(self):self.directories=set()
    def __call__(self,path):
        path=Path(os.path.abspath(path))
        for p in (path,*path.parents):
            if p!=path and p in self.directories:continue
            info=os.lstat(p)
            require(not stat.S_ISLNK(info.st_mode) and not(getattr(info,'st_file_attributes',0)&1024),'Linked provider source/object path')
            if p==path:require(stat.S_ISREG(info.st_mode),'Regular provider source/object required')
            else:self.directories.add(p)
        with path.open('rb') as stream:return hashlib.file_digest(stream,'sha256').hexdigest()


def clean_status(root):
    # Fixed platform checkout policy, never an input option. Git source objects
    # stay pinned; exact raw source/object bytes are independently fingerprinted.
    return git(root,'-c','core.autocrlf='+CHECKOUT_EOL,'status','--porcelain','--untracked-files=all')


def configuration():
    c=load_bytes(CONFIG.read_bytes())
    require(c['repository']==PROVIDER_REPO and c['commit']==PROVIDER_COMMIT and c['toolchain']==PROVIDER_LEAN,'Selected provider pin drift')
    require(c['module']==MODULE and [r['declaration'] for r in c['apis']]==list(SELECTED_APIS) and set(c['allowed_axioms'])==ALLOWED,'Selected provider inventory drift')
    require(c['mode']=='POLICY_ADAPTER_ONLY' and c['model_optimality']=='NOT_ESTABLISHED','Provider policy capability escalation')
    return c


def source_closure(root):
    """Only selected provider-owned imports, in dependency order."""
    seen=set();visiting=set();order=[]
    def visit(name):
        p=root.joinpath(*name.split('.')).with_suffix('.lean')
        if not p.is_file():return
        require(name not in visiting,'Provider import cycle')
        if name in seen:return
        require(len(seen)<256,'Selected source closure budget exceeded')
        visiting.add(name)
        for imported in IMPORT.findall(p.read_text(encoding='utf-8')):visit(imported)
        visiting.remove(name);seen.add(name);order.append(name)
    visit(MODULE);require(order and order[-1]==MODULE,'Selected source module missing');return order


def provider_identity(root):
    root=unlinked(root).resolve();require(root.is_dir() and root!=HOST,'Separate provider checkout required')
    c=configuration();require(git(root,'rev-parse','HEAD')==PROVIDER_COMMIT,'Wrong provider commit')
    require(not clean_status(root),'Provider source must be clean')
    require((root/'lean-toolchain').read_text(encoding='utf-8').strip()==PROVIDER_LEAN,'Wrong provider toolchain pin')
    require(file_hash(root/c['source_path'])==c['source_sha256'] and file_hash(root/'lake-manifest.json')==c['lake_manifest_sha256'],'Pinned provider source/manifest bytes differ')
    manifest=load_bytes((root/'lake-manifest.json').read_bytes());require(manifest['packagesDir']=='.lake/packages','Provider package path override')
    packages={};source_hash=BatchHasher()
    for p in manifest['packages']:
        require(p['type']=='git' and type(p['name'])is str and re.fullmatch('[A-Za-z0-9_-]+',p['name']) is not None,'Unsupported provider package')
        path=unlinked(root/'.lake/packages'/p['name']).resolve()
        require(path.is_dir() and git(path,'rev-parse','HEAD')==p['rev'],'Missing or wrong pinned provider package: '+p['name'])
        require(not clean_status(path),'Dirty provider dependency: '+p['name'])
        files=[s for s in git(path,'ls-files','-z').split('\0') if s and (s.endswith('.lean') or s in ('lean-toolchain','lakefile.lean','lakefile.toml','lake-manifest.json'))]
        raw={s:source_hash(path/s) for s in files}
        packages[p['name']]={'commit':p['rev'],'tree':git(path,'rev-parse','HEAD^{tree}'),'url':p['url'],
          'raw_source_file_count':len(raw),'raw_source_sha256':digest(raw,domain='OPICA_PROVIDER_PACKAGE_SOURCE_BYTES_V1')}
    modules=source_closure(root)
    return {'repository':PROVIDER_REPO,'commit':PROVIDER_COMMIT,'tree':git(root,'rev-parse','HEAD^{tree}'),
      'toolchain':PROVIDER_LEAN,'packages':packages,
      'checkout_core_autocrlf':CHECKOUT_EOL,
      'source_sha256':{m.replace('.','/')+'.lean':file_hash(root/(m.replace('.','/')+'.lean')) for m in modules},
      'pin_sha256':{p:file_hash(root/p) for p in ('lean-toolchain','lakefile.toml','lake-manifest.json')},
      'runner_sha256':{str(p.relative_to(HOST)).replace('\\','/'):file_hash(p) for p in (Path(__file__),CONFIG,TEMPLATE,HERE/'canonical.py',HERE/'snapshot.py',HERE.parents[1]/'permansson/opica_composition.py')}}


def _external(path,root):
    p=unlinked(path).resolve();require(not p.is_relative_to(HOST) and not p.is_relative_to(root),'Provider evidence must be outside source');return p


def recorded_producer_root(value):
    require(type(value)is str and value,'Original producer output path required')
    p=PureWindowsPath(value) if re.match(r'^[A-Za-z]:[\\/]',value) else PurePosixPath(value)
    require(p.is_absolute() and '..' not in p.parts and str(p)==value,'Noncanonical original producer output path')
    return p


def command(argv,cwd,env,output,label,seconds=180):
    require(type(seconds)is int and 1<=seconds<=600,'Bounded provider command deadline required')
    out=output/(label+'.stdout.log');err=output/(label+'.stderr.log');started=time.monotonic()
    with out.open('xb') as a,err.open('xb') as b:
        try:code=subprocess.run(argv,cwd=cwd,env=env,stdout=a,stderr=b,timeout=seconds,check=False).returncode;timeout=False
        except subprocess.TimeoutExpired:code=None;timeout=True
    record={'argv':list(map(str,argv)),'returncode':code,'timeout':timeout,'elapsed_ms':int((time.monotonic()-started)*1000),
      'stdout':out.name,'stderr':err.name,'stdout_sha256':file_hash(out),'stderr_sha256':file_hash(err)}
    return record


def parse_audit(raw):
    rows=[];modules=None
    for line in raw.decode('utf-8',errors='strict').splitlines():
        if line.startswith(MARKER):rows.append(load_bytes(line[len(MARKER):].encode()))
        elif line.startswith(MODULE_MARKER):
            require(modules is None,'Duplicate provider module export');modules=load_bytes(line[len(MODULE_MARKER):].encode())
    expected=configuration()['apis']
    require(len(rows)==3 and [r['declaration'] for r in rows]==list(SELECTED_APIS),'Missing selected provider audit')
    for r,e in zip(rows,expected):
        require(set(r)=={'declaration','consumer','type_expression','consumer_type_expression','proof_value_expression','axioms','consumer_axioms'} and r['consumer']==e['consumer'],'Independent consumer inventory differs')
        for key in ('type_expression','consumer_type_expression','proof_value_expression'):require(type(r[key])is str and r[key],'Missing exact compiler expression')
        for key in ('axioms','consumer_axioms'):require(type(r[key])is list and set(r[key])<=ALLOWED and len(r[key])==len(set(r[key])),'Unapproved transitive provider axiom')
    require(type(modules)is list and len(modules)<=20000 and len(modules)==len(set(modules)) and MODULE in modules and all(type(m)is str and len(m)<=512 and re.fullmatch('[A-Za-z_][A-Za-z0-9_.]*',m) for m in modules),'Missing complete imported module inventory')
    return rows,modules


def object_inventory(modules,paths,prefix,root,fresh):
    result={};object_hash=BatchHasher()
    for m in modules:
        rel=Path(*m.split('.')).with_suffix('.olean');matches=[base/rel for base in [*paths,prefix/'lib/lean'] if (base/rel).is_file()]
        require(matches,'Imported provider/package object missing: '+m);p=unlinked(matches[0]).resolve()
        if m.startswith(('PermanssonLean.','PermanssonResearch.')):require(p.is_relative_to(fresh),'Stale provider object crossed fresh-build boundary')
        result[m]={}
        for suffix in ('','.private','.server'):
            actual=Path(str(p)+suffix)
            if actual.is_file():result[m]['olean'+suffix]=object_hash(actual)
    return result


def produce(provider_root,output,lake=None,seconds_per_command=180):
    root=unlinked(provider_root).resolve();before=provider_identity(root);output=_external(output,root)
    require(not output.exists(),'Fresh provider output required');output.mkdir(parents=True)
    report={'schema':'OPICA_SELECTED_PROVIDER_NATIVE_V1','status':'NOT_ADMITTED','source':before,'commands':[],'producer_root':str(output),
      'mode':'POLICY_ADAPTER_ONLY','host_theorem_authority':False,'model_optimality':'NOT_ESTABLISHED','RH':'OPEN','Step4':'OPEN'}
    env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','ELAN_'))}
    env.update({'ELAN_TOOLCHAIN':PROVIDER_LEAN,'LEAN_NUM_THREADS':'2','GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'})
    lake=str(unlinked(lake or shutil.which('lake') or 'lake').resolve())
    def run(argv,cwd,env,label):
        r=command(argv,cwd,env,output,label,seconds_per_command)
        report['commands'].append(r)
        require(r['returncode']==0 and r['timeout'] is False,'Native provider command failed: '+label)
        return r
    try:
        helper='import json,os,shutil;print(json.dumps({"LEAN_PATH":os.environ.get("LEAN_PATH",""),"PATH":os.environ["PATH"],"lean":shutil.which("lean")}))'
        r=run([lake,'env',sys.executable,'-c',helper],root,env,'environment')
        resolved=json.loads((output/r['stdout']).read_text(encoding='utf-8'))
        lean=unlinked(resolved['lean']).resolve();require(lean.is_file(),'Provider Lean binary absent')
        r=run([str(lean),'--version'],root,env,'compiler')
        version=(output/r['stdout']).read_text(encoding='utf-8').strip();require('version 4.34.0,' in version,'Provider compiler must be Lean4.34.0')
        r=run([str(lean),'--print-prefix'],root,env,'prefix')
        prefix=unlinked((output/r['stdout']).read_text(encoding='utf-8').strip()).resolve();require(lean.is_relative_to(prefix),'Wrong provider compiler prefix')
        paths=[]
        for p in resolved['LEAN_PATH'].split(os.pathsep):
            path=unlinked(root/p).resolve()
            if path.is_relative_to(root/'.lake/build'):continue
            require(path.is_relative_to(root/'.lake/packages') or path==prefix/'lib/lean','Foreign host/cache path in provider environment')
            require(not path.exists() or path.is_dir(),'Provider import path is not a directory');paths.append(path)
        fresh=output/'objects';fresh.mkdir();native={**env,'PATH':resolved['PATH'],'LEAN_PATH':os.pathsep.join(map(str,[fresh,*paths])),'LEAN_SYSROOT':str(prefix)}
        report['environment']={'compiler':version,'compiler_sha256':file_hash(lean),'lake_sha256':file_hash(lake),
          'compiler_prefix':str(prefix),'package_paths':list(map(str,paths)),'selected_build':'FRESH_SELECTED_TRANSITIVE_PROVIDER_SOURCE_CLOSURE'}
        report['environment']['absent_search_paths']=[str(p) for p in paths if not p.exists()]
        for i,m in enumerate(source_closure(root)):
            source=root/(m.replace('.','/')+'.lean');obj=fresh/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
            r=run([str(lean),'-R',str(root),'-o',str(obj),str(source)],root,native,'module-'+str(i).zfill(3))
        audit=output/'ProviderAudit.lean';audit.write_bytes(TEMPLATE.read_bytes())
        r=run([str(lean),'-R',str(output),'-o',str(output/'ProviderAudit.olean'),str(audit)],output,native,'consumers')
        rows,modules=parse_audit((output/r['stdout']).read_bytes());report['audits']=rows
        report['imported_objects']=object_inventory(modules,[fresh,*paths],prefix,root,fresh)
        report['audit_source_sha256']=file_hash(audit)
        require(provider_identity(root)==before,'Provider source/packages changed during build')
        report['status']='COMPILED_SELECTED_PROVIDER_PENDING_INDEPENDENT_REPLAY';return report
    finally:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')


def verify(provider_root,artifact_root,replay_output,lake=None,seconds_per_command=180):
    root=unlinked(provider_root).resolve();artifact=_external(artifact_root,root);fresh=_external(replay_output,root)
    require(not fresh.is_relative_to(artifact),'Replay must leave all input artifacts immutable')
    report=load_bytes((artifact/'result.json').read_bytes())
    require(type(report)is dict and set(report)=={'schema','status','source','commands','producer_root','mode','host_theorem_authority','model_optimality','RH','Step4','environment','audits','imported_objects','audit_source_sha256'},'Closed complete provider receipt required')
    require(report.get('schema')=='OPICA_SELECTED_PROVIDER_NATIVE_V1' and report.get('status')=='COMPILED_SELECTED_PROVIDER_PENDING_INDEPENDENT_REPLAY','Selected native provider result missing')
    require(report['source']==provider_identity(root),'Stale provider source/package/runtime receipt')
    require(report.get('mode')=='POLICY_ADAPTER_ONLY' and report.get('host_theorem_authority') is False and report.get('model_optimality')=='NOT_ESTABLISHED' and report.get('RH')=='OPEN' and report.get('Step4')=='OPEN','Provider claim escalation')
    closure=source_closure(root);labels=['environment','compiler','prefix',*['module-'+str(i).zfill(3) for i in range(len(closure))],'consumers']
    original=recorded_producer_root(report['producer_root'])
    require(type(report['commands'])is list and len(report['commands'])==len(labels),'Incomplete selected native command inventory')
    require(all(type(c)is dict and type(c.get('argv'))is list and c['argv'] and all(type(s)is str for s in c['argv']) for c in report['commands']),'Invalid selected command argv')
    compiler=report['commands'][1]['argv'][0]
    for c,label in zip(report['commands'],labels):
        require(type(c)is dict and set(c)=={'argv','returncode','timeout','elapsed_ms','stdout','stderr','stdout_sha256','stderr_sha256'},'Closed provider command record required')
        require(type(c['returncode'])is int and c['returncode']==0 and c['timeout'] is False,'Provider command incomplete')
        require(type(c['elapsed_ms'])is int and c['elapsed_ms']>=0 and type(c['argv'])is list and all(type(s)is str for s in c['argv']),'Invalid native execution receipt')
        for key in ('stdout','stderr'):
            name=c[key];require(name==label+'.'+key+'.log','Wrong ordered native raw log')
            require((artifact/name).stat().st_size<=32*1024*1024,'Provider raw log resource budget exceeded')
            require(file_hash(artifact/name)==c[key+'_sha256'],'Changed provider raw log')
    require(report['commands'][1]['argv']==[compiler,'--version'] and report['commands'][2]['argv']==[compiler,'--print-prefix'],'Wrong compiler identity commands')
    for c,m in zip(report['commands'][3:-1],closure):
        require(c['argv']==[compiler,'-R',str(root),'-o',str(original/'objects'/(m.replace('.','/')+'.olean')),str(root/(m.replace('.','/')+'.lean'))],'Selected provider native build was replaced')
    require(report['commands'][-1]['argv']==[compiler,'-R',str(original),'-o',str(original/'ProviderAudit.olean'),str(original/'ProviderAudit.lean')],'Wrong independent expected-type consumer command')
    r=report['commands'][-1];rows,modules=parse_audit((artifact/r['stdout']).read_bytes())
    require(rows==report['audits'] and file_hash(artifact/'ProviderAudit.lean')==file_hash(TEMPLATE)==report['audit_source_sha256'],'Changed independent consumer or compiler export')
    require(object_inventory(modules,[artifact/'objects',*[Path(p) for p in report['environment']['package_paths']]],
      Path(report['environment']['compiler_prefix']),root,artifact/'objects')==report['imported_objects'],'Changed actual imported producer/package objects')
    replay=produce(root,fresh,lake,seconds_per_command)
    for field in ('source','environment','audits','imported_objects','audit_source_sha256'):require(report[field]==replay[field],'Independent provider replay differs: '+field)
    raw={r['declaration']:r for r in replay['audits']}
    policy={'repository':PROVIDER_REPO,'commit':PROVIDER_COMMIT,'toolchain':PROVIDER_LEAN,'environment':replay['environment'],
      'apis':list(SELECTED_APIS),'raw_evidence':raw,'mode':'POLICY_ADAPTER_ONLY'}
    admitted=qualify_provider(policy,expected_environment=replay['environment'],replay=lambda name,row:row==raw[name])
    result={'schema':'OPICA_SELECTED_PROVIDER_ACCEPTANCE_V1',**admitted,'source':replay['source'],'environment':replay['environment'],
      'selected_apis':list(SELECTED_APIS),'compiled_source_modules':len(replay['source']['source_sha256']),
      'imported_object_modules':len(replay['imported_objects']),'producer_receipt_sha256':file_hash(artifact/'result.json'),
      'independent_receipt_sha256':file_hash(fresh/'result.json'),'RH':'OPEN','Step4':'OPEN'}
    (fresh/'acceptance.json').write_bytes(canonical_bytes(result)+b'\n');return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--provider-root',required=True,type=Path);p.add_argument('--output-dir',required=True,type=Path)
    p.add_argument('--lake',type=Path);p.add_argument('--verify',type=Path);p.add_argument('--seconds-per-command',type=int,default=180);a=p.parse_args()
    try:
        result=verify(a.provider_root,a.verify,a.output_dir,a.lake,a.seconds_per_command) if a.verify else produce(a.provider_root,a.output_dir,a.lake,a.seconds_per_command)
        print(json.dumps({'status':result['status'],'mode':'POLICY_ADAPTER_ONLY'}));return 0
    except (ContractError,OSError,ValueError,subprocess.SubprocessError) as exc:
        print(json.dumps({'status':'NOT_ADMITTED','reason':str(exc)}));return 1


if __name__=='__main__':raise SystemExit(main())
