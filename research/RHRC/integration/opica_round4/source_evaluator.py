"""Portable bounded producer/checker/lane for six prescribed K4/K5 probes."""
from __future__ import annotations
import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import uuid

HERE=Path(__file__).resolve().parent
import importlib.util
def _module(name,path):
    if name in sys.modules:return sys.modules[name]
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec)
    sys.modules[name]=m;spec.loader.exec_module(m);return m
B=_module('_opica4_source_backend',HERE/'source_backend.py')
CASES=HERE/'fixtures/source_cases.json'
EXPECTED_IDS=['K4_Q3_FIVE_FOURTHS','K5_Q5_SEVEN_FOURTHS','K5_LOG4_SEAM','K5_Q4_MODIFIED_Q2_HALF','K4_Q2_ENTERING_Q2','K4_Q4_ENTERING_Q4']
EXPECTED_INPUTS=[
 (4,3,{'kind':'rational','value':'5/4'},'VON_MANGOLDT','1',None),
 (5,5,{'kind':'rational','value':'7/4'},'VON_MANGOLDT','1',None),
 (5,4,{'kind':'log_integer','n':4},'VON_MANGOLDT','1',None),
 (5,4,{'kind':'rational','value':'3/2'},'MODIFIED_Q2_NOT_ZETA','1/2',None),
 (4,2,{'kind':'scaled_log_integer','n':2,'scale':'10/9'},'VON_MANGOLDT','1',2),
 (4,4,{'kind':'scaled_log_integer','n':4,'scale':'10/9'},'VON_MANGOLDT','1',4)]


def prescribed_cases():
    doc=B.strict_json(CASES.read_bytes(),32768)
    B.require(type(doc)is dict and set(doc)=={'schema','cases'} and doc['schema']=='OPICA4_FINITE_SOURCE_CASES_V1','Closed case manifest required')
    cases=doc['cases'];B.require(type(cases)is list and [c.get('id') for c in cases]==EXPECTED_IDS,'Exact six-case inventory required')
    for c,expected in zip(cases,EXPECTED_INPUTS):
        B.validate_request(c)
        K,Q,aperture,kind,multiplier,entering=expected
        B.require(B.identical(c,{'id':c['id'],'K':K,'Q':Q,'aperture':aperture,
          'source':{'kind':kind,'prime2_multiplier':multiplier},'entering_atom':entering}),'Changed prescribed mathematical input')
    return cases


def external(path):
    p=B.unlinked(path).resolve();B.require(not p.is_relative_to(B.REPO),'Evidence must be outside checkout');return p


def runtime_identity():
    import flint
    package=Path(flint.__file__).resolve().parent
    native=list(package.glob('*.pyd'))+list(package.glob('*.so'))
    shared=package.parent/'python_flint.libs'
    if shared.is_dir():native.extend(p for p in shared.iterdir() if p.is_file())
    return {'python_executable':str(Path(sys.executable).resolve()),'python_executable_sha256':B.digest(sys.executable),
      'python_version':platform.python_version(),'python_optimized':bool(sys.flags.optimize),
      'python_flint_version':flint.__version__,'python_flint_module_sha256':B.digest(flint.__file__),
      'flint_version':flint.__FLINT_VERSION__,'native_library_sha256':{str(p):B.digest(p) for p in sorted(native)},
      'platform':platform.platform()}


def worker(case_id,bits,target,direct=False):
    case=next((c for c in prescribed_cases() if c['id']==case_id),None)
    B.require(case is not None,'Unknown prescribed case')
    target=external(target);B.require(not target.exists(),'Worker output must be fresh')
    identity=B.source_identity();started=datetime.now(timezone.utc).isoformat();runid=str(uuid.uuid4())
    try:
        result=B.evaluate_request(case,bits,'direct' if direct else 'unit',112 if direct else 80)
    except B.Unresolved as exc:result={'request':case,'status':'UNRESOLVED','reason':str(exc),'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**B.CAPS}
    B.require(B.identical(identity,B.source_identity()),'Source changed during native computation')
    result['execution']={'run_id':runid,'started_utc':started,'finished_utc':datetime.now(timezone.utc).isoformat(),
      'source_identity':identity,'runtime':runtime_identity(),'argv':sys.argv,'producer_kind':'DIRECT_CHECKER' if direct else 'UNIT_PRODUCER'}
    target.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'case':case_id,'status':result['status'],'run_id':runid}))
    return 0 if result['status']=='FINITE_ENCLOSURES' else 2


def evaluate(output,bits=256,seconds=60,require_clean=True):
    cases=prescribed_cases();B.require(type(bits)is int and bits in (256,512),'Producer precision256/512 required')
    B.require(type(seconds)is int and 1<=seconds<=60,'Worker wall budget1..60 seconds required')
    output=external(output);B.require(not output.exists(),'Refuse evidence overwrite')
    identity=B.source_identity();B.require(not require_clean or identity['clean'],'Public lane requires clean committed checkout')
    B.require(identity['head']==os.environ.get('REQUESTED_HEAD',identity['head']),'Requested head mismatch')
    output.mkdir(parents=True)
    report={'schema':'OPICA4_FINITE_SOURCE_EVALUATOR_V1','status':'UNRESOLVED','source_identity':identity,
      'producer_root':str(output),
      'checked_commit':identity['head'],'checked_tree':identity['tree'],'runtime':runtime_identity(),
      'precision_bits':bits,'seconds_per_case':seconds,'case_manifest_sha256':B.digest(CASES),'cases':[],
      'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**B.CAPS}
    try:
        for case in cases:
            name=case['id'];target=output/(name+'.json');out=output/(name+'.stdout.log');err=output/(name+'.stderr.log')
            argv=[sys.executable,*(['-O'] if sys.flags.optimize else []),'-B',str(HERE/'source_evaluator.py'),'--_worker',name,
              '--precision-bits',str(bits),'--worker-output',str(target)]
            begin=time.monotonic()
            with out.open('xb') as a,err.open('xb') as b:
                try:
                    code=subprocess.run(argv,cwd=B.REPO,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONUTF8':'1'},stdout=a,stderr=b,timeout=seconds,check=False).returncode;timeout=False
                except subprocess.TimeoutExpired:code=None;timeout=True
            if timeout or not target.is_file():
                value={'request':case,'status':'UNRESOLVED','reason':'WORKER_WALL_DEADLINE' if timeout else 'WORKER_NO_RECORD',**B.CAPS}
                target.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
            value=B.strict_json(target.read_bytes())
            report['cases'].append({'id':name,'request':case,'outcome':value['status'],'file':target.name,'sha256':B.digest(target),
              'command':{'argv':argv,'returncode':code,'timeout':timeout,'elapsed_ms':int((time.monotonic()-begin)*1000),
              'stdout':out.name,'stderr':err.name,'stdout_sha256':B.digest(out),'stderr_sha256':B.digest(err)}})
        B.require(B.identical(B.source_identity(),identity),'Source changed during evaluator')
        if all(x['outcome']=='FINITE_ENCLOSURES' and x['command']['returncode']==0 for x in report['cases']):report['status']='PASS_FINITE_SOURCE_ENCLOSURES'
        return report
    finally:(output/'result.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')


def lane(output,bits=256,seconds=60,require_clean=True):
    output=external(output);B.require(not output.exists(),'Lane output must be fresh');output.mkdir(parents=True)
    for mode in ('normal','optimized'):
        argv=[sys.executable,*(['-O'] if mode=='optimized' else []),'-B',str(HERE/'source_evaluator.py'),
          '--output-dir',str(output/mode),'--precision-bits',str(bits),'--seconds-per-case',str(seconds)]
        if not require_clean:argv.append('--allow-dirty-development')
        with (output/(mode+'.stdout.log')).open('xb') as out,(output/(mode+'.stderr.log')).open('xb') as err:
            code=subprocess.run(argv,stdout=out,stderr=err,timeout=6*seconds+30,check=False).returncode
        B.require(code==0,'Producer mode incomplete: '+mode)
    C=_module('_opica4_source_checker',HERE/'source_checker.py')
    result=C.verify_evaluator_evidence(output,recompute_output=output.parent/(output.name+'-independent'),require_clean=require_clean)
    (output/'lane.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',type=Path);p.add_argument('--precision-bits',type=int,default=256)
    p.add_argument('--seconds-per-case',type=int,default=60);p.add_argument('--lane',action='store_true');p.add_argument('--check',type=Path)
    p.add_argument('--allow-dirty-development',action='store_true',help='Development evidence remains explicitly nonaccepting')
    p.add_argument('--_worker');p.add_argument('--_verify-worker');p.add_argument('--worker-output',type=Path)
    a=p.parse_args()
    try:
        if a._worker or a._verify_worker:
            B.require(a.worker_output is not None and a.output_dir is None and not(a._worker and a._verify_worker),'Closed worker invocation required')
            return worker(a._worker or a._verify_worker,a.precision_bits,a.worker_output,bool(a._verify_worker))
        B.require(a.output_dir is not None,'Fresh external output required')
        if a.check:
            C=_module('_opica4_source_checker',HERE/'source_checker.py');result=C.verify_evaluator_evidence(a.check,recompute_output=a.output_dir,require_clean=not a.allow_dirty_development)
        elif a.lane:result=lane(a.output_dir,a.precision_bits,a.seconds_per_case,not a.allow_dirty_development)
        else:result=evaluate(a.output_dir,a.precision_bits,a.seconds_per_case,not a.allow_dirty_development)
        print(json.dumps({'status':result['status'],'RH':'OPEN','Step4':'OPEN'}));return 0 if result['status'].startswith('PASS_') or result['status']=='DEVELOPMENT_RECOMPUTED_FINITE_SOURCE' else 1
    except (B.InvalidRequest,B.Unresolved,OSError,ValueError) as exc:
        print(json.dumps({'status':'INVALID_OR_UNRESOLVED','reason':str(exc),**B.CAPS}));return 1


if __name__=='__main__':raise SystemExit(main())
