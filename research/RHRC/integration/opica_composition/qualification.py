"""Actual current-child Lean preparation and source-bound qualification gates.

The root cache build has one owner. All candidate drivers and independent
outputs live in the CI-provisioned bounded native volume. No historical atlas,
theorem, source pin or generated parent file is rewritten here.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import asdict
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time
from .canonical import require,canonical_bytes,load_bytes,digest,ContractError
from .contracts import WorkerConfig,SearchBudget,as_record
from .snapshot import unlinked,file_hash,git
from .executor import run_worker,worker_environment,lean_name,lean_string
from .inventory import expression_hash,validate_telescope

ATLAS='research/RHRC/integration/opica_round3/atlas/CONSTRAINT_ATLAS.jsonl'
ATLAS_SHA256='c0becd027e18be98c29647b85e0d18aeb0748a66c2c6ab6690a4940b2945150e'
LEAN_PIN='leanprover/lean4:v4.33.0-rc2'
CORE_MODULES=(
 'Zeta23.RHRC.OpicaComposition.Protocol','Zeta23.RHRC.OpicaComposition.Elaborate',
 'Zeta23.RHRC.OpicaComposition.Export','Zeta23.RHRC.OpicaComposition.Audit',
 'Zeta23.RHRC.OpicaComposition.FiniteWorlds','Zeta23.OPICAComposition.Calibration',
 'Zeta23.RHRC.OpicaComposition.Validation','Zeta23.RHRC.OpicaComposition.ResearchTargets',
 'Zeta23.RHRC.RegisteredClaimBindings','Zeta23.RHRC.DeclarationDependencyExport',
 'Zeta23.RHRC.SourceCandidateResolution',
 'Zeta23.OPICARound4.Validation','Zeta23.RHRC.OpicaRound3AtlasExport')
COHORTS={'UCDP_HISTORICAL216':216,'UCDP_CONTACT185':185,'OPICA_FOLLOWUP100':100,
 'OPICA_ORIGINAL76':76,'REVIEWED_SUPPORT_IDENTITY':51,'OPICA_ROUND2_40':40,
 'UCDP_PRIORITY_TRIPLE18':18,'ROUND3_INDEPENDENT_CONSUMERS5':5,'OPICA_ROUND3_5':5}
ATLAS_FIELDS={'schema','declaration','module','kind','universe_parameters','type_text','type_expression',
 'outer_telescope','conclusion_text','type_constants','value_constants','structure_constants','axioms'}


def _packages(repo):
    manifest=load_bytes((repo/'lake-manifest.json').read_bytes());require(manifest['packagesDir']=='.lake/packages','Package location override')
    result={}
    for row in manifest['packages']:
        require(row['type']=='git' and re.fullmatch('[A-Za-z0-9_-]+',row['name']) and re.fullmatch('[0-9a-f]{40}',row['rev']),'Unsupported pinned package')
        root=unlinked(repo/'.lake/packages'/row['name']).resolve()
        require(git(root,'rev-parse','HEAD')==row['rev'],'Actual package revision differs: '+row['name'])
        require(not git(root,'-c','core.autocrlf=false','status','--porcelain','--untracked-files=all'),'Dirty native package source: '+row['name'])
        result[row['name']]={'commit':row['rev'],'tree':git(root,'rev-parse','HEAD^{tree}'),'url':row['url']}
    require(result.get('mathlib',{}).get('commit')=='51e6992efd06126df61a496bebf8f49482a4e129','Host Mathlib pin drift')
    return result


def _worker_version(repo,output,worker):
    require(Path(worker.lean).resolve().is_relative_to(Path(worker.toolchain_root).resolve()),'Worker compiler prefix differs')
    env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','ELAN_'))}
    c=_command([worker.lean,'--version'],repo,env,output,'worker-version',30)
    require(c['returncode']==0 and not c['timeout'],'Actual worker compiler unavailable')
    text=(output/c['stdout']).read_text(encoding='utf-8').strip()
    require(text.startswith('Lean (version 4.33.0-rc2,') and 'd8b18978322de05a8f3dba51ef03cf5461676c17' in text,'Wrong current-child worker compiler')
    return c


def frozen_atlas(repo):
    repo=unlinked(repo).resolve();path=repo/ATLAS
    require(file_hash(path)==ATLAS_SHA256,'Frozen atlas bytes changed')
    rows=[load_bytes(line) for line in path.read_bytes().splitlines() if line]
    require(len(rows)==462 and len({r['declaration'] for r in rows})==462,'Exact462-declaration atlas required')
    counts=Counter(m['cohort'] for r in rows for m in r['memberships'])
    require(dict(counts)==COHORTS and sum(counts.values())==696,'Frozen696 cohort memberships differ')
    for row in rows:
        lean_name(row['declaration']);lean_name(row['module'])
        source=row['source'];require(source['path']==row['module'].replace('.','/')+'.lean','Atlas source/module origin differs')
        require(file_hash(repo/source['path'])==source['sha256'],'Frozen atlas mathematical source changed: '+source['path'])
        require(expression_hash(row['statement']['type_expression'])==row['type_sha256'],'Frozen atlas type digest differs')
    return rows


def _external(repo,output,production):
    repo=unlinked(repo).resolve();output=unlinked(output).resolve()
    require(not output.is_relative_to(repo),'Native qualification output must be outside source')
    if production:
        require(platform.system()=='Linux','Production native qualification requires Linux')
        value=os.environ.get('OPICA_NATIVE_OUTPUT');require(value,'OPICA_NATIVE_OUTPUT bounded volume is required')
        native=unlinked(value).resolve();require(native.is_dir() and output.is_relative_to(native),'All native qualification outputs must remain in OPICA_NATIVE_OUTPUT')
    require(not output.exists(),'Fresh native qualification output required');output.mkdir(parents=True);return output


def _command(argv,repo,env,output,label,seconds):
    stdout=output/(label+'.stdout.log');stderr=output/(label+'.stderr.log');started=time.monotonic()
    with stdout.open('xb') as a,stderr.open('xb') as b:
        try:code=subprocess.run(argv,cwd=repo,env=env,stdout=a,stderr=b,timeout=seconds,check=False).returncode;timeout=False
        except subprocess.TimeoutExpired:code=None;timeout=True
    return {'argv':list(map(str,argv)),'returncode':code,'timeout':timeout,'elapsed_ms':int((time.monotonic()-started)*1000),
      'stdout':stdout.name,'stderr':stderr.name,'stdout_sha256':file_hash(stdout),'stderr_sha256':file_hash(stderr)}


def _source(repo,modules):
    paths={m.replace('.','/')+'.lean' for m in modules}|{'lean-toolchain','lake-manifest.json','lakefile.toml',ATLAS}
    return {p:file_hash(repo/p) for p in sorted(paths)}


def prepare_native(repo,output):
    """Single-owner Linux bootstrap; root calls this after the implementation freeze."""
    require(platform.system()=='Linux','Production native preparation requires Linux')
    repo=unlinked(repo).resolve();require((repo/'lean-toolchain').read_text(encoding='utf-8').strip()==LEAN_PIN,'Host toolchain pin drift')
    require(not git(repo,'status','--porcelain','--untracked-files=all'),'Production native preparation requires clean source')
    packages=_packages(repo)
    rows=frozen_atlas(repo);modules=sorted(set(CORE_MODULES)|{r['module'] for r in rows})
    before=_source(repo,modules);output=_external(repo,output,True)
    report={'schema':'OPICA_NATIVE_PREPARATION_V1','status':'ENVIRONMENT_ERROR','commands':[],
      'checked_commit':git(repo,'rev-parse','HEAD'),'checked_tree':git(repo,'rev-parse','HEAD^{tree}'),
      'source_sha256':before,'requested_modules':modules,'RH':'OPEN','Step4':'OPEN'}
    report['pinned_packages']=packages
    env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','ELAN_'))}
    env.update({'ELAN_TOOLCHAIN':LEAN_PIN,'LEAN_NUM_THREADS':'2','GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'})
    lake=shutil.which('lake');require(lake,'Pinned host Lake is missing')
    def run(argv,label,seconds=60):
        c=_command(argv,repo,env,output,label,seconds);report['commands'].append(c)
        require(c['returncode']==0 and c['timeout'] is False,'Native preparation command failed: '+label);return output/c['stdout']
    try:
        mount=load_bytes(run(['/usr/bin/findmnt','--json','--bytes','--target',os.environ['OPICA_NATIVE_OUTPUT'],'--output','FSTYPE,SIZE,TARGET'],'volume').read_bytes())
        fs=mount['filesystems'];require(len(fs)==1 and fs[0]['fstype']=='tmpfs' and 0<int(fs[0]['size'])<=SearchBudget().disk_bytes,'Actual native tmpfs volume is absent or exceeds disk budget')
        report['native_volume']=fs[0]
        version=run([lake,'env','lean','--version'],'compiler').read_text(encoding='utf-8').strip()
        require(version.startswith('Lean (version 4.33.0-rc2,') and 'd8b18978322de05a8f3dba51ef03cf5461676c17' in version,'Wrong actual host compiler')
        prefix=unlinked(run([lake,'env','lean','--print-prefix'],'prefix').read_text(encoding='utf-8').strip()).resolve()
        lean=unlinked(run([lake,'env','which','lean'],'lean-path').read_text(encoding='utf-8').strip()).resolve()
        require(lean.is_relative_to(prefix),'Host Lean binary/prefix mismatch')
        run([lake,'build',*modules],'selected-build',7200)
        text=run([lake,'env','printenv','LEAN_PATH'],'import-paths').read_text(encoding='utf-8').strip()
        paths=[]
        for p in text.split(os.pathsep):
            path=unlinked(repo/p).resolve()
            require(path.is_relative_to(repo/'.lake') or path==prefix/'lib/lean','Foreign compiler/import cache path')
            if path.is_dir() and str(path) not in paths:paths.append(str(path))
        require(str(repo/'.lake/build/lib/lean') in paths,'Fresh host object root absent')
        budget=asdict(SearchBudget());worker=WorkerConfig(str(lean),str(prefix),paths,production=True,budget=budget)
        summary=worker_environment(worker,manifest_output=output/'native-objects.json')
        require(_source(repo,modules)==before and _packages(repo)==packages and git(repo,'rev-parse','HEAD')==report['checked_commit'],'Source changed during native preparation')
        report.update({'status':'PASS_NATIVE_PREPARED','worker':worker.to_dict(),'worker_environment':summary,
          'native_objects_sha256':file_hash(output/'native-objects.json'),'compiler':version,'worker_config_path':str(output/'worker.json')})
        (output/'worker.json').write_bytes(canonical_bytes(worker.to_dict())+b'\n');return report
    finally:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')


def atlas_driver(rows):
    modules=sorted({r['module'] for r in rows}|{'Zeta23.RHRC.OpicaRound3AtlasExport'})
    text='\n'.join('import '+lean_name(m) for m in modules)
    text+='\nset_option pp.fullNames true\nset_option pp.universes true\nrun_cmd do\n  Zeta23.RHRC.OpicaRound3AtlasExport.exportAtlas #[\n'
    text+=',\n'.join('    { declaration := '+lean_string(r['declaration'])+', moduleName := '+lean_string(r['module'])+' }' for r in rows)
    return text+'\n  ]\n'


def check_current_compatibility(repo,output,worker):
    worker=as_record(worker,WorkerConfig);repo=unlinked(repo).resolve();rows=frozen_atlas(repo)
    output=_external(repo,output,worker.production);before=_source(repo,{r['module'] for r in rows}|{'Zeta23.RHRC.OpicaRound3AtlasExport'})
    report={'schema':'OPICA_CURRENT_COMPATIBILITY_V1','status':'ENVIRONMENT_ERROR','batches':[],
      'checked_commit':git(repo,'rev-parse','HEAD'),'checked_tree':git(repo,'rev-parse','HEAD^{tree}'),
      'atlas_sha256':ATLAS_SHA256,'source_sha256':before,'RH':'OPEN','Step4':'OPEN','semantic_exhaustion':False}
    all_rows={};budget=SearchBudget(**worker.budget) if worker.budget else SearchBudget()
    native_export=output/'native-export.jsonl';native_export.write_bytes(b'')
    try:
        report['worker_version_command']=_worker_version(repo,output,worker)
        for index,start in enumerate(range(0,len(rows),16)):
            batch=rows[start:start+16];folder=output/('batch-'+str(index).zfill(3));folder.mkdir()
            source='AtlasBatch'+str(index).zfill(3)+'.lean';obj=source[:-5]+'.olean'
            (folder/source).write_text(atlas_driver(batch),encoding='utf-8',newline='\n')
            native=run_worker(worker,folder,source,obj,budget);report['batches'].append({'index':index,'declarations':[r['declaration'] for r in batch],'native':native})
            require(native['resource_status'] is None and native['exit_code']==0,'Fresh current atlas batch failed or exceeded resources')
            raw=(folder/(source+'.log')).read_bytes();require(len(raw)<8*1024*1024,'Current atlas batch log exceeds8MiB')
            wanted={r['declaration']:r for r in batch};seen=set()
            for line in raw.splitlines():
                if not line.startswith(b'OPICA3_ATLAS\t'):continue
                fact=load_bytes(line.split(b'\t',1)[1]);require(type(fact)is dict and set(fact)==ATLAS_FIELDS and fact['schema']=='OPICA3_ATLAS_COMPILER_ROW_V1','Malformed actual atlas compiler row')
                name=fact['declaration'];require(name in wanted and name not in seen and name not in all_rows,'Wrong/duplicate current atlas declaration')
                old=wanted[name];require(fact['module']==old['module'] and fact['kind']==old['kind'],'Current declaration source origin/kind changed')
                require(expression_hash(fact['type_expression'])==old['type_sha256'],'Current declaration exact type changed: '+name)
                require(fact['axioms']==old['statement']['axioms'] and set(fact['axioms'])<={'propext','Classical.choice','Quot.sound'},'Current declaration full axiom footprint changed')
                require(fact['universe_parameters']==old['statement']['universe_parameters'],'Current universe parameters changed')
                validate_telescope(fact['type_expression'],fact['outer_telescope'])
                with native_export.open('ab') as stream:stream.write(line+b'\n')
                seen.add(name);all_rows[name]={'declaration':name,'module':fact['module'],'type_sha256':old['type_sha256'],'axioms':fact['axioms']}
            require(seen==set(wanted),'Current atlas batch omitted required declarations')
            require((folder/obj).is_file(),'Fresh current atlas object absent')
            report['batches'][-1]['source_sha256']=file_hash(folder/source);report['batches'][-1]['object_sha256']=file_hash(folder/obj)
        require(len(all_rows)==462 and _source(repo,{r['module'] for r in rows}|{'Zeta23.RHRC.OpicaRound3AtlasExport'})==before,'Current atlas source changed during export')
        report.update({'status':'PASS_CURRENT_COMPATIBILITY' if worker.production else 'DEVELOPMENT_CURRENT_COMPATIBILITY',
          'declarations':462,'memberships':696,'required_root_memberships':221,'historical_contacts':185,
          'cohorts':COHORTS,'semantic_review_promotion':False,'compiler_rows':list(all_rows.values()),
          'native_export_path':str(native_export),'native_export_sha256':file_hash(native_export)})
        return report
    finally:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')


def check_mathematical_support(repo,output,worker):
    worker=as_record(worker,WorkerConfig);repo=unlinked(repo).resolve();output=_external(repo,output,worker.production)
    gate=repo/'research/RHRC/integration/opica_round4/math_gate.py';require(gate.is_file(),'Actual mathematical support gate missing')
    version=_worker_version(repo,output,worker)
    env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONUTF8':'1'}
    command=[sys.executable,'-B',str(gate),'--repo',str(repo),'--output-dir',str(output/'native'),
      '--lean',worker.lean,'--lean-paths',os.pathsep.join(worker.lean_paths)]
    record=_command(command,repo,env,output,'mathematical-support',7200)
    report={'schema':'OPICA_MATHEMATICAL_SUPPORT_QUALIFICATION_V1','status':'ENVIRONMENT_ERROR','command':record,
      'gate_sha256':file_hash(gate),'RH':'OPEN','Step4':'OPEN'}
    report['worker_version_command']=version
    try:
        require(record['returncode']==0 and record['timeout'] is False,'Actual mathematical support gate failed')
        result=load_bytes((output/'native/result.json').read_bytes())
        require(result.get('status')=='PASS' and result.get('module_count')==16 and result.get('declaration_count')==98 and result.get('semantic_mutation_count')==4,'Mathematical support gate incomplete or not actual native evidence')
        report.update({'status':'PASS_MATHEMATICAL_SUPPORT' if worker.production else 'DEVELOPMENT_MATHEMATICAL_SUPPORT',
          'native_result':result,'native_result_sha256':file_hash(output/'native/result.json')});return report
    finally:(output/'result.json').write_bytes(canonical_bytes(report)+b'\n')
