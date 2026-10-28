"""Independently recompute complete-source point enclosures, with open claims.

The checker changes variables back to [0,L] and uses higher-precision Arb
quadrature. Inclusion of that enclosure in every claimed interval is required;
mere intersection, a producer boolean, and a zero-containing ball do not pass.
The source formula and python-flint remain explicit numerical trust providers.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import source_backend as B
import source_evaluator as E

PASS_STATUS='PASS_RECOMPUTED_FINITE_SOURCE_EVALUATOR'
REPORT_FIELDS={'schema','status','checked_commit','checked_tree','source_identity','backend_version',
 'python_optimized','precision_bits','seconds_per_case','case_manifest_sha256','cases','authority',
 'is_zero_generated_detector',*B.CAPS}
CASE_FIELDS={'request','status','backend_version','representation','precision_bits','export_bits','cutoff',
 'enclosures','construction','budgets','authority','is_zero_generated_detector',*B.CAPS}


def plain(path,root):
    path=B.unlinked(path);root=B.unlinked(root).resolve()
    B.require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root),
              'Missing, linked, or escaping evidence file')
    return path


def caps(value):
    B.require(all(k in value and type(value[k])is type(v) and value[k]==v for k,v in B.CAPS.items()),
              'Finite-only claim firewall was changed')
    B.require(value.get('authority')=='FINITE_INTERVAL_EVIDENCE_ONLY'
              and value.get('is_zero_generated_detector') is False,'Numerical authority escalation')


def interval(value):
    B.require(type(value)is dict and set(value)=={'lower','upper'},'Closed rational interval required')
    low,high=B.endpoint(value['lower']),B.endpoint(value['upper'])
    B.require(low<=high and high-low<=B.MAX_WIDTH,'Reversed or overbudget enclosure')
    return low,high


def compare_enclosures(claimed,refined,path='enclosures'):
    """Validate exact shape and outward containment at every numerical leaf."""
    if type(refined)is dict:
        B.require(type(claimed)is dict and set(claimed)==set(refined),'Changed enclosure fields: '+path)
        if set(refined)=={'lower','upper'}:
            low,high=interval(claimed);rlo,rhi=interval(refined)
            B.require(low<=rlo<=rhi<=high,'Refined direct enclosure is not contained: '+path)
            return 1
        return sum(compare_enclosures(claimed[k],v,path+'.'+k) for k,v in refined.items())
    if type(refined)is list:
        B.require(type(claimed)is list and len(claimed)==len(refined),'Changed enclosure length: '+path)
        return sum(compare_enclosures(a,b,path+'['+str(i)+']') for i,(a,b) in enumerate(zip(claimed,refined)))
    if path.endswith('.sign'):
        # A wider valid enclosure may honestly leave a sign unresolved.
        B.require(claimed in ('STRICT_POSITIVE','STRICT_NEGATIVE','UNRESOLVED_SIGN'),'Invalid sign classification')
        return 0
    B.require(type(claimed)is type(refined) and claimed==refined,'Changed exact construction: '+path)
    return 0


def contains_zero_sum(a,b,minus=False):
    al,ah=interval(a);bl,bh=interval(b)
    return al-bh<=0<=ah-bl if minus else al+bl<=0<=ah+bh


def consistency(value):
    """Consistency checks are not proofs inferred from a zero-containing ball."""
    enc=value['enclosures'];M=enc['matrix_real'];N=2*value['request']['K']+1
    B.require(len(M)==N and all(len(row)==N for row in M),'Wrong actual matrix dimension')
    for i in range(N):
        for j in range(N):
            B.require(contains_zero_sum(M[i][j],M[j][i],True),'Hermitian symmetry consistency failed')
    for parity in ('even','odd'):
        geo=enc['geometry'][parity]
        B.require(interval(geo['normal_norm_sq'])[0]>0,'Uncertified pole-normal denominator')
        native=enc['neutral'][parity]
        if value['request']['K']==2:
            B.require(native=={'status':'EMPTY_BY_EXACT_CARRIER_DIMENSION','dimension':0,'rayleigh_bottom':None},
                      'K2 empty carrier was assigned a fake bottom')
        else:
            B.require(interval(native['gram'])[0]>0,'Uncertified seed Gram')
            low,high=interval(native['rayleigh_bottom'])
            sign='STRICT_POSITIVE' if low>0 else 'STRICT_NEGATIVE' if high<0 else 'UNRESOLVED_SIGN'
            B.require(native['sign']==sign,'Sign not certified by the exported interval')
    if value['request']['K']==3:
        c=enc['source_correction']
        for a,b,p,q in zip(c['native_intertwining_defect'],c['corrected_rank_one_vector'],
                          c['projected_legal_defect'],c['projected_odd_output_residual']):
            B.require(contains_zero_sum(a,b,True),'Corrected source identity consistency failed')
            al,ah=interval(a);pl,ph=interval(p);ql,qh=interval(q)
            B.require(al-ph-qh<=0<=ah-pl-ql,'Projected output residual was omitted')
    effect=enc['prime_power_4_effect']
    if effect is not None:
        B.require(type(effect['strict_negative'])is bool and effect['strict_negative']==
                  (interval(effect['full_00_minus_missing_4_00'])[1]<0),'Unsupported q4 sign')


def compare_case(claimed,refined,case,bits):
    B.require(type(claimed)is dict and set(claimed)==CASE_FIELDS,'Closed complete case evidence required')
    caps(claimed)
    B.validate_request(claimed['request'])
    B.require(B.identical(claimed['request'],case) and claimed['status']=='FINITE_ENCLOSURES','Wrong actual source case')
    B.require(claimed['backend_version']=='0.9.0' and claimed['representation']=='unit'
              and type(claimed['precision_bits'])is int and claimed['precision_bits']==bits
              and type(claimed['export_bits'])is int and claimed['export_bits']==80,'Wrong producer method')
    B.require(B.identical(claimed['cutoff'],refined['cutoff']) and B.identical(claimed['construction'],refined['construction']),
              'Changed source domain, cutoff, basis, or theorem anchors')
    expected=dict(refined['budgets']);expected['quadrature_tolerance_exponent']=-(bits-24)
    B.require(B.identical(claimed['budgets'],expected),'Changed resource/error budget')
    count=compare_enclosures(claimed['enclosures'],refined['enclosures'])
    consistency(claimed)
    return count


def command_record(record,directory,case,bits,optimized):
    B.require(type(record)is dict and set(record)=={'argv','returncode','timeout','elapsed_ms','stdout','stderr',
              'stdout_sha256','stderr_sha256'},'Closed native worker command record required')
    B.require(type(record['returncode'])is int and record['returncode']==0 and record['timeout'] is False
              and type(record['elapsed_ms'])is int and record['elapsed_ms']>=0,'Worker did not complete successfully')
    argv=record['argv'];B.require(type(argv)is list and all(type(x)is str for x in argv),'Invalid worker argv')
    prefix=2 if optimized else 1
    B.require(len(argv)==prefix+8 and bool(argv[0]) and (not optimized or argv[1]=='-O'),
              'Wrong Python worker mode')
    tail=argv[prefix:]
    B.require(tail[0]=='-B' and tail[1].replace('\\','/').endswith('/research/RHRC/integration/opica_round3/source_evaluator.py')
              and tail[2:6]==['--_worker',case['id'],'--precision-bits',str(bits)]
              and tail[6]=='--worker-output' and tail[7].replace('\\','/').rsplit('/',1)[-1]==case['id']+'.json',
              'Wrong actual worker command')
    for stream in ('stdout','stderr'):
        B.require(record[stream]==case['id']+'.'+stream+'.log','Unexpected raw log name')
        file=plain(directory/record[stream],directory)
        B.require(file.stat().st_size<=65536 and B.digest(file)==record[stream+'_sha256'],'Changed worker raw log')
    out=B.strict_json((directory/record['stdout']).read_bytes(),65536)
    B.require(out=={'case':case['id'],'status':'FINITE_ENCLOSURES'} and
              not (directory/record['stderr']).read_bytes(),'Worker raw result did not certify the actual case')


def recompute_case(case,bits,directory):
    """Bound the independent direct-integral computation in its own process."""
    output=directory/(case['id']+'.json')
    argv=[sys.executable,'-B',str(HERE/'source_evaluator.py'),'--_verify-worker',case['id'],
          '--precision-bits',str(bits),'--worker-output',str(output)]
    stdout=directory/(case['id']+'.stdout.log');stderr=directory/(case['id']+'.stderr.log')
    with stdout.open('xb') as out,stderr.open('xb') as err:
        try:
            result=subprocess.run(argv,cwd=B.REPO,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONUTF8':'1'},
                                  stdout=out,stderr=err,timeout=30,check=False)
        except subprocess.TimeoutExpired as exc:raise B.Unresolved('INDEPENDENT_CHECKER_WALL_DEADLINE') from exc
    B.certain(result.returncode==0 and output.is_file(),'INDEPENDENT_CHECKER_DID_NOT_ENCLOSE')
    value=B.strict_json(output.read_bytes());caps(value)
    B.certain(value.get('status')=='FINITE_ENCLOSURES' and value.get('representation')=='direct'
              and value.get('precision_bits')==bits and value.get('export_bits')==112,
              'INDEPENDENT_CHECKER_DID_NOT_ENCLOSE')
    return value


def verify_evaluator_evidence(repo,artifact_root,expected_head,expected_tree,recompute=True,recompute_output=None,
                              artifact_collection_root=None):
    B.require(recompute is True,'Acceptance requires actual independent recomputation')
    B.require(Path(repo).resolve()==B.REPO.resolve(),'Checker must run in the current pinned source checkout')
    root=E.external(artifact_root);B.require(root.is_dir(),'Missing evaluator artifact root')
    collection=E.external(artifact_collection_root) if artifact_collection_root is not None else root
    B.require(root.is_relative_to(collection),'Artifact root escapes its immutable collection')
    before=B.source_identity(repo)
    B.require(before['clean'] and before['head']==expected_head and before['tree']==expected_tree,
              'Wrong or dirty checker source')
    cases=E.prescribed_cases();reports={};claimed={}
    for mode in ('normal','optimized'):
        directory=root/'source-evaluator'/mode
        doc=B.strict_json(plain(directory/'result.json',root).read_bytes())
        B.require(type(doc)is dict and set(doc)==REPORT_FIELDS,'Closed evaluator report required');caps(doc)
        B.require(doc['schema']=='OPICA3_FINITE_SOURCE_EVALUATOR_V1' and doc['status']=='PASS_FINITE_SOURCE_ENCLOSURES',
                  'Required actual source evaluations are incomplete')
        B.require(doc['checked_commit']==expected_head and doc['checked_tree']==expected_tree
                  and B.identical(doc['source_identity'],before),'Evaluator source/head/tree mismatch')
        B.require(doc['backend_version']=='0.9.0' and doc['python_optimized'] is (mode=='optimized')
                  and type(doc['precision_bits'])is int and doc['precision_bits'] in (128,256,512)
                  and type(doc['seconds_per_case'])is int and 1<=doc['seconds_per_case']<=60
                  and doc['case_manifest_sha256']==B.digest(E.CASES),'Wrong evaluator backend/mode/cases/budgets')
        B.require(type(doc['cases'])is list and len(doc['cases'])==len(cases),'Required actual case missing')
        for row,case in zip(doc['cases'],cases):
            B.require(type(row)is dict and set(row)=={'id','request','outcome','file','sha256','command'}
                      and row['id']==case['id'] and B.identical(row['request'],case) and row['outcome']=='FINITE_ENCLOSURES'
                      and row['file']==case['id']+'.json','Changed or missing actual case result')
            file=plain(directory/row['file'],root)
            B.require(B.digest(file)==row['sha256'],'Case digest mismatch')
            command_record(row['command'],directory,case,doc['precision_bits'],mode=='optimized')
            claimed[(mode,case['id'])]=B.strict_json(file.read_bytes())
        reports[mode]=doc
    # One higher-precision direct recomputation per source point, shared by the
    # two Python modes; those modes are still separately bound to raw executions.
    # The entire downloaded artifact collection is immutable input. Never add
    # siblings inside it; optional retained output belongs to the caller's
    # separate acceptance-output directory.
    if recompute_output is None:
        base=B.unlinked(tempfile.gettempdir()).resolve()
        B.require(not base.is_relative_to(collection) and not base.is_relative_to(B.REPO.resolve()),
                  'Independent checker TEMP must be outside source and input artifacts')
        directory=Path(tempfile.mkdtemp(prefix='opica3-source-check-',dir=base))
    else:
        directory=E.external(recompute_output)
        B.require(not directory.is_relative_to(collection) and not directory.exists(),
                  'Recomputation output must be fresh and outside all input artifacts')
        directory.mkdir(parents=True)
    comparisons=0;hashes={}
    for case in cases:
        bits=max(256,2*max(d['precision_bits'] for d in reports.values()))
        refined=recompute_case(case,bits,directory);hashes[case['id']]=B.digest(directory/(case['id']+'.json'))
        for mode in reports:
            comparisons+=compare_case(claimed[(mode,case['id'])],refined,case,reports[mode]['precision_bits'])
    effect=claimed[('normal','K3_Q4_THREE_HALVES')]['enclosures']['prime_power_4_effect']
    B.require(interval(effect['full_00_minus_missing_4_00'])[1]<0,'Actual missing-q4 falsifier was not certified')
    B.require(B.source_identity(repo)==before,'Checker source changed during recomputation')
    return {'status':PASS_STATUS,'checked_commit':expected_head,'checked_tree':expected_tree,
            'modes':['normal','optimized'],'case_ids':E.EXPECTED_IDS,'independently_recomputed_cases':len(cases),
            'contained_interval_comparisons':comparisons,'recompute_directory':str(directory),
            'direct_case_sha256':hashes,'hermiticity':'EXACT_SYMMETRY_OF_POLE_PRIME_AND_ALPHA_DIFFERENCE_FORMULAS',
            'identity_ball_checks':'CONSISTENCY_ONLY_NOT_PROOF_OR_KERNEL_CERTIFICATION',
            'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**B.CAPS}
