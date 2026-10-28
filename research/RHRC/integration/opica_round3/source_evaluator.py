"""Prescribed complete-source point probes in isolated bounded Arb workers."""
from __future__ import annotations
import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import source_backend as B

CASES=HERE/'fixtures/source_evaluator_cases.json'
EXPECTED_IDS=['K2_Q1_HALF','K3_Q4_THREE_HALVES','K3_LOG2_SEAM']
EXPECTED_CASES=[
 {'id':'K2_Q1_HALF','K':2,'Q':1,'aperture':{'kind':'rational','value':'1/2'}},
 {'id':'K3_Q4_THREE_HALVES','K':3,'Q':4,'aperture':{'kind':'rational','value':'3/2'}},
 {'id':'K3_LOG2_SEAM','K':3,'Q':2,'aperture':{'kind':'log_integer','n':2}},
]


def prescribed_cases(path=CASES):
    path=Path(path)
    B.require(path.resolve()==CASES.resolve(),'Only the prescribed current source case file is allowed')
    doc=B.strict_json(path.read_bytes(),16384)
    B.require(type(doc)is dict and set(doc)=={'schema','cases'} and doc['schema']=='OPICA3_FINITE_SOURCE_CASES_V1',
              'Closed prescribed-case manifest required')
    B.require(type(doc['cases'])is list and B.identical(doc['cases'],EXPECTED_CASES),
              'Exact three prescribed actual source cases required')
    for case in doc['cases']:B.validate_request(case)
    return doc['cases']


def external(path):
    path=B.unlinked(path).resolve()
    B.require(not path.is_relative_to(B.REPO.resolve()),'Evidence must be external')
    return path


def worker(case_id,bits,output,verify=False):
    cases={row['id']:row for row in prescribed_cases()}
    B.require(case_id in cases,'Unknown prescribed case')
    output=external(output)
    B.require(output.parent.is_dir() and not output.exists(),'Fresh worker output required')
    try:
        result=B.evaluate_request(cases[case_id],bits,'direct' if verify else 'unit',112 if verify else 80)
    except B.InvalidRequest as exc:
        result={'request':cases[case_id],'status':'INVALID','reason':str(exc),**B.CAPS}
    except (B.Unresolved,ArithmeticError,ValueError,OverflowError) as exc:
        result={'request':cases[case_id],'status':'UNRESOLVED','reason':str(exc),**B.CAPS}
    output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'case':case_id,'status':result['status']}))
    return 0 if result['status']=='FINITE_ENCLOSURES' else 2


def evaluate(cases_path,output,bits,seconds):
    cases=prescribed_cases(cases_path)
    B.require(type(bits)is int and bits in (128,256,512),'Producer precision128/256/512 required')
    B.require(type(seconds)is int and 1<=seconds<=60,'Worker wall budget1..60 seconds required')
    output=external(output)
    B.require(not output.exists(),'Refuse to overwrite evaluator evidence')
    identity=B.source_identity()
    B.require(identity['clean'],'Public source evidence needs a clean committed checkout')
    B.require(identity['head']==os.environ.get('REQUESTED_HEAD',identity['head']),'Another requested head')
    output.mkdir(parents=True)
    report={'schema':'OPICA3_FINITE_SOURCE_EVALUATOR_V1','status':'UNRESOLVED',
        'checked_commit':identity['head'],'checked_tree':identity['tree'],'source_identity':identity,
        'backend_version':'0.9.0','python_optimized':bool(sys.flags.optimize),'precision_bits':bits,
        'seconds_per_case':seconds,'case_manifest_sha256':B.digest(CASES),'cases':[],
        'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**B.CAPS}
    try:
        for case in cases:
            name=case['id'];target=output/(name+'.json')
            argv=[sys.executable,*(['-O'] if sys.flags.optimize else []),'-B',str(Path(__file__).resolve()),
                  '--_worker',name,'--precision-bits',str(bits),'--worker-output',str(target)]
            started=time.monotonic()
            stdout,stderr=output/(name+'.stdout.log'),output/(name+'.stderr.log')
            with stdout.open('xb') as out,stderr.open('xb') as err:
                try:
                    code=subprocess.run(argv,cwd=B.REPO,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONUTF8':'1'},
                        stdout=out,stderr=err,timeout=seconds,check=False).returncode
                    timeout=False
                except subprocess.TimeoutExpired:
                    code=None;timeout=True
            if timeout:
                value={'request':case,'status':'UNRESOLVED','reason':'WORKER_WALL_DEADLINE',**B.CAPS}
                target.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
            elif not target.is_file():
                value={'request':case,'status':'UNRESOLVED','reason':'WORKER_DID_NOT_PRODUCE_EVIDENCE',**B.CAPS}
                target.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
            value=B.strict_json(target.read_bytes())
            report['cases'].append({'id':name,'request':case,'outcome':value['status'],'file':target.name,
                'sha256':B.digest(target),'command':{'argv':argv,'returncode':code,'timeout':timeout,
                    'elapsed_ms':int((time.monotonic()-started)*1000),'stdout':stdout.name,'stderr':stderr.name,
                    'stdout_sha256':B.digest(stdout),'stderr_sha256':B.digest(stderr)}})
        B.require(B.source_identity()==identity,'Source changed during evaluation')
        if all(r['outcome']=='FINITE_ENCLOSURES' and r['command']['returncode']==0 for r in report['cases']):
            q4=B.strict_json((output/'K3_Q4_THREE_HALVES.json').read_bytes())
            effect=q4['enclosures']['prime_power_4_effect']['full_00_minus_missing_4_00']
            B.require(B.endpoint(effect['upper'])<0,'Required actual prime-power4 effect was not certified')
            report['status']='PASS_FINITE_SOURCE_ENCLOSURES'
        return report
    finally:
        (output/'result.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',type=Path,default=CASES)
    parser.add_argument('--output-dir',type=Path)
    parser.add_argument('--precision-bits',type=int,default=128)
    parser.add_argument('--seconds-per-case',type=int,default=30)
    parser.add_argument('--_worker',help=argparse.SUPPRESS)
    parser.add_argument('--_verify-worker',help=argparse.SUPPRESS)
    parser.add_argument('--worker-output',type=Path,help=argparse.SUPPRESS)
    args=parser.parse_args()
    try:
        if args._worker or args._verify_worker:
            B.require(args.worker_output is not None and args.output_dir is None,'Exact internal worker arguments required')
            B.require(not (args._worker and args._verify_worker),'Only one internal worker mode allowed')
            return worker(args._worker or args._verify_worker,args.precision_bits,args.worker_output,bool(args._verify_worker))
        B.require(args.output_dir is not None,'External output directory required')
        result=evaluate(args.cases,args.output_dir,args.precision_bits,args.seconds_per_case)
        print(json.dumps({'status':result['status'],'checked_commit':result['checked_commit'],**B.CAPS}))
        return 0 if result['status']=='PASS_FINITE_SOURCE_ENCLOSURES' else 1
    except (B.InvalidRequest,OSError,ValueError) as exc:
        print(json.dumps({'status':'INVALID','reason':str(exc),**B.CAPS}))
        return 1


if __name__=='__main__':raise SystemExit(main())
