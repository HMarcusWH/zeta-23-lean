"""Independent [0,L] Arb reconstruction and source/execution-bound acceptance.

Every exported interval must contain its independently refined counterpart.
The checker rebuilds physical bases from constraints, generalized metrics,
all correction terms and spectral projectors from the mathematical request.
It never promotes a zero-containing interval or an unresolved root cluster.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
import importlib.util
def _module(name,path):
    if name in sys.modules:return sys.modules[name]
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec)
    sys.modules[name]=m;spec.loader.exec_module(m);return m
E=_module('_opica4_source_evaluator',HERE/'source_evaluator.py');B=E.B
PASS_STATUS='PASS_RECOMPUTED_FINITE_SOURCE_EVALUATOR'


def caps(value):
    B.require(all(type(value.get(k))is type(v) and value[k]==v for k,v in B.CAPS.items()),'Changed finite claim firewall')
    B.require(value.get('authority')=='FINITE_INTERVAL_EVIDENCE_ONLY' and value.get('is_zero_generated_detector') is False,'Numerical authority escalation')


def interval(x):
    B.require(type(x)is dict and set(x)=={'lower','upper'},'Closed rational interval required')
    lo,hi=B.endpoint(x['lower']),B.endpoint(x['upper'])
    B.require(lo<=hi and hi-lo<=B.MAX_WIDTH,'Reversed or overbudget interval');return lo,hi


def compare_enclosures(claimed,refined,path='enclosures'):
    if type(refined)is dict:
        B.require(type(claimed)is dict and set(claimed)==set(refined),'Changed enclosure shape: '+path)
        if set(refined)=={'lower','upper'}:
            lo,hi=interval(claimed);rl,rh=interval(refined)
            B.require(lo<=rl<=rh<=hi,'Direct refined interval not contained: '+path);return 1
        return sum(compare_enclosures(claimed[k],v,path+'.'+k) for k,v in refined.items())
    if type(refined)is list:
        B.require(type(claimed)is list and len(claimed)==len(refined),'Changed enclosure length: '+path)
        return sum(compare_enclosures(x,y,path+'['+str(i)+']') for i,(x,y) in enumerate(zip(claimed,refined)))
    B.require(B.identical(claimed,refined),'Changed exact field: '+path);return 0


def disposition(value):
    """Require the actual falsification conclusions, without universal claims."""
    caps(value);enc=value['enclosures'];name=value['request']['id'];s=enc['spectrum']
    for parity in ('even','odd'):
        p=enc['physical'][parity];d=value['request']['K']-2
        B.require(p['dimension']==d and p['zero_index']==0 and p['negative_index']+p['positive_index']==d,'Wrong physical dimension/inertia')
        B.require(all(not(lo<=0<=hi) for lo,hi in map(interval,p['eigenvalues'])),'Near zero cannot certify inertia or kernel')
        bounds=[interval(x) for x in p['eigenvalues']]
        B.require(all(bounds[i][1]<bounds[i+1][0] for i in range(len(bounds)-1)),'Overlapping exported roots cannot certify simple groups')
        B.require(p['negative_index']==sum(interval(x)[1]<0 for x in p['eigenvalues']),'Unsupported negative index')
    residues=[interval(g['residue']) for g in s['groups']]
    B.require(all(g['multiplicity']==1 for g in s['groups']),'Unresolved source cluster must not be assigned simple authority')
    signed=interval(s['signed_response_at_zero']);mass=interval(s['positive_reciprocal_mass'])
    if name=='K4_Q3_FIVE_FOURTHS':
        B.require(any(hi<0 for lo,hi in residues) and any(lo>0 for lo,hi in residues) and signed[1]<1,'Required K4 mixed-residue falsifier missing')
    if name=='K5_Q5_SEVEN_FOURTHS':
        B.require(mass[0]>1 and signed[1]<1 and interval(s['residue_sum'])[1]<0,'K5 cancellation/mass-overflow missing')
        D=s['negative_derivative_at_minus_t']
        B.require(interval(D['0'])[0]>0 and interval(D['21/50'])[0]>0 and interval(D['43/100'])[1]<0,'K5 derivative-switch falsifier missing')
    if name=='K5_LOG4_SEAM':
        B.require(value['cutoff']['entering_atom']=='EXACT_ZERO_BY_qBasis_aperture_eq_zero' and value['cutoff']['summed_through']==3,'Exact seam was replaced by floating-floor convention')
        B.require([a['q'] for a in enc['prime_power_atoms']]==[2,3] and all(lo>0 for lo,hi in residues),'Wrong seam arithmetic or residues')
    if name=='K5_Q4_MODIFIED_Q2_HALF':
        B.require(value['source']['kind']=='MODIFIED_Q2_NOT_ZETA' and enc['physical']['even']['negative_index']==1 and enc['physical']['odd']['negative_index']==0 and signed[0]>1,'Modified-source control changed')
        B.require([(a['q'],a['multiplier']) for a in enc['prime_power_atoms']]==[(2,'1/2'),(3,'1'),(4,'1')],'q2 modification incorrectly changed q4')
    atom=enc['entering_atom_control']
    if atom is not None:
        for p in atom['parities'].values():B.require(interval(p['determinant'])[1]<0,'Entering atom determinant is not strictly negative')
        B.require(atom['source']=='ENTERING_ATOM_ONLY_NOT_COMPLETE_SOURCE','Atom signature escalated to complete source')


def scientific_disposition(value):
    disposition(value);name=value['request']['id'];s=value['enclosures']['spectrum']
    historical={
      'K4_Q3_FIVE_FOURTHS':('K4_5_4','MIXED_SIGNED_RESIDUES_WITH_POSITIVE_PARITY_FORMS'),
      'K5_Q5_SEVEN_FOURTHS':('K5_7_4','SIGNED_CANCELLATION_POSITIVE_MASS_OVERFLOW_AND_DERIVATIVE_SWITCH'),
      'K5_LOG4_SEAM':('K5_LOG4','POSITIVE_PARITY_FORMS_AND_POSITIVE_RESIDUES_AT_EXACT_SEAM'),
      'K5_Q4_MODIFIED_Q2_HALF':('K5_3_2_MODIFIED_PRIME2_HALF','SOURCE_BLIND_POSITIVE_COEFFICIENT_INFERENCE_FALSIFIED'),
      'K4_Q2_ENTERING_Q2':('PRIME_SEAM_Q2_DELTA_1_10','ENTERING_ATOM_INDEFINITE_BOTH_PARITIES'),
      'K4_Q4_ENTERING_Q4':(None,'NEW_PRIME_POWER_Q4_ENTERING_ATOM_CONTROL')}
    old,meaning=historical[name];positive=all(value['enclosures']['physical'][p]['negative_index']==0 for p in ('even','odd'))
    return {'status':'CERTIFIED_FINITE_POINT_FALSIFICATION_CONTROL','scientific_result':meaning,
      'historical_case':old,'historical_comparison':'SAME_FINITE_QUALITATIVE_DISPOSITION' if old else 'NEW_SOURCE_BOUND_CONTROL',
      'historical_authority':'UNAUTHENTICATED_MPMATH_IV_OR_NONCERTIFIED_RESEARCH_NOT_REBOUND_TO_CURRENT_HEAD',
      'historical_audit_reference':{'document':'CODE_NUMERICS_PROVENANCE_REVIEW.json','sha256':'2eeb2cec6328def3e8abb5565502b83b3a5f4a633371f60ad0de5539ca6dd17e',
        'K45_certify_extended_source_cells.py_sha256':'4884b5a240d31cb6776d1902958eb342c1f7f2f46550d5cd9cc5f1a3f3c2f0c8',
        'use':'HISTORICAL_QUALITATIVE_COMPARISON_ONLY_NOT_CURRENT_EXECUTION_AUTHORITY'},
      'actual_source':value['source'],'both_parity_forms_strictly_positive':positive,
      'endpoint_response_below_one':interval(s['signed_response_at_zero'])[1]<1,
      'positive_reciprocal_mass_exceeds_one':interval(s['positive_reciprocal_mass'])[0]>1,
      'interpretation':'Positive A and B imply S(0)<1 through 1-S(0)=det(A)/det(B); favorable endpoints supply no independent arithmetic bound.' if positive else 'Modified q2 source is a generic finite falsifier and is not the zeta source.',
      'scope':'FINITE_POINT_ONLY;NO_REGULAR_CELL_OR_UNIVERSAL_ARITHMETIC_RESTRICTION;RH_AND_STEP4_OPEN'}


def compare_case(claimed,refined,case,bits):
    required=set(refined)-{'execution'}
    B.require(type(claimed)is dict and set(claimed) in (required,required|{'execution'}),'Closed complete case record required')
    caps(claimed);B.validate_request(claimed['request'])
    B.require(B.identical(claimed['request'],case) and claimed['schema']=='OPICA4_FINITE_SOURCE_CASE_V1' and claimed['status']=='FINITE_ENCLOSURES','Wrong source case')
    B.require(claimed['representation']=='unit' and claimed['precision_bits']==bits and type(claimed['precision_bits'])is int and claimed['export_bits']==80 and type(claimed['export_bits'])is int,'Wrong producer representation/precision')
    for field in ('source','cutoff','construction','backend_version'):B.require(B.identical(claimed[field],refined[field]),'Changed '+field)
    budget=dict(refined['budgets']);budget['quadrature_tolerance_exponent']=-(bits-32)
    B.require(B.identical(claimed['budgets'],budget),'Changed error/resource budget')
    count=compare_enclosures(claimed['enclosures'],refined['enclosures']);disposition(claimed);return count


def plain(path,root):
    p=B.unlinked(path);B.require(p.is_file() and p.resolve().is_relative_to(root),'Missing or escaping evidence file');return p


def execution(value,identity,case,bits,direct=False,optimized=False):
    x=value.get('execution');B.require(type(x)is dict and set(x)=={'run_id','started_utc','finished_utc','source_identity','runtime','argv','producer_kind'},'Every accepted record needs execution identity')
    import uuid
    try:B.require(str(uuid.UUID(x['run_id']))==x['run_id'],'Invalid execution UUID')
    except (ValueError,TypeError,AttributeError) as exc:raise B.InvalidRequest('Missing execution UUID') from exc
    B.require(B.identical(x['source_identity'],identity),'Record source execution identity mismatch')
    expected=E.runtime_identity();expected['python_optimized']=optimized
    B.require(B.identical(x['runtime'],expected),'Record runtime identity mismatch')
    B.require(x['producer_kind']==('DIRECT_CHECKER' if direct else 'UNIT_PRODUCER'),'Wrong executing representation')
    B.require(type(x['started_utc'])is str and type(x['finished_utc'])is str and x['started_utc']<=x['finished_utc'],'Bad execution time bounds')
    argv=x['argv'];B.require(type(argv)is list and len(argv)==7,'Wrong actual executed argv')
    B.require(Path(argv[0]).resolve()==HERE/'source_evaluator.py' and argv[1:5]==['--_verify-worker' if direct else '--_worker',case['id'],'--precision-bits',str(bits)] and argv[5]=='--worker-output' and Path(argv[6]).name==case['id']+'.json','Wrong actual executed case command')


def recompute_case(case,bits,directory):
    output=directory/(case['id']+'.json');out=directory/(case['id']+'.stdout.log');err=directory/(case['id']+'.stderr.log')
    argv=[E.python_executable(),'-B',str(HERE/'source_evaluator.py'),'--_verify-worker',case['id'],'--precision-bits',str(bits),'--worker-output',str(output)]
    with out.open('xb') as a,err.open('xb') as b:
        try:code=subprocess.run(argv,cwd=B.REPO,stdout=a,stderr=b,timeout=60,check=False).returncode
        except subprocess.TimeoutExpired as exc:raise B.Unresolved('INDEPENDENT_CHECKER_WALL_DEADLINE') from exc
    B.certain(code==0 and output.is_file(),'INDEPENDENT_CHECKER_DID_NOT_ENCLOSE')
    value=B.strict_json(output.read_bytes());B.certain(value.get('representation')=='direct' and value.get('export_bits')==112,'Wrong direct checker output')
    return value


def verify_evaluator_evidence(artifact_root,recompute_output,require_clean=True,expected_head=None,expected_tree=None):
    root=E.external(artifact_root);B.require(root.is_dir(),'Missing numerical artifact root');identity=B.source_identity()
    B.require(not require_clean or identity['clean'],'Acceptance requires clean committed source')
    B.require(expected_head is None or expected_head==identity['head'],'Wrong requested head')
    B.require(expected_tree is None or expected_tree==identity['tree'],'Wrong requested tree')
    cases=E.prescribed_cases();claims={};reports={};runids=set()
    fields={'schema','status','source_identity','producer_root','checked_commit','checked_tree','runtime','precision_bits','seconds_per_case','case_manifest_sha256','cases','authority','is_zero_generated_detector',*B.CAPS}
    for mode in ('normal','optimized'):
        directory=root/mode;doc=B.strict_json(plain(directory/'result.json',root).read_bytes())
        B.require(type(doc)is dict and set(doc)==fields,'Closed numerical report required');caps(doc)
        original=B.recorded_root(doc['producer_root'])
        B.require(doc['schema']=='OPICA4_FINITE_SOURCE_EVALUATOR_V1' and doc['status']=='PASS_FINITE_SOURCE_ENCLOSURES','Mandatory numerical case unresolved')
        B.require(B.identical(doc['source_identity'],identity) and doc['checked_commit']==identity['head'] and doc['checked_tree']==identity['tree'],'Wrong producer source commit/tree/bytes')
        runtime=E.runtime_identity();runtime['python_optimized']=mode=='optimized'
        B.require(B.identical(doc['runtime'],runtime) and type(doc['precision_bits'])is int and doc['precision_bits'] in (256,512),'Wrong runtime or precision')
        B.require(type(doc['seconds_per_case'])is int and 1<=doc['seconds_per_case']<=60 and doc['case_manifest_sha256']==B.digest(E.CASES),'Wrong resource/case manifest')
        B.require(type(doc['cases'])is list and len(doc['cases'])==len(cases),'Mandatory numerical case missing')
        for row,case in zip(doc['cases'],cases):
            B.require(type(row)is dict and set(row)=={'id','request','outcome','file','sha256','command'} and row['id']==case['id'] and B.identical(row['request'],case) and row['outcome']=='FINITE_ENCLOSURES' and row['file']==case['id']+'.json','Changed exact case row')
            file=plain(directory/row['file'],root);B.require(B.digest(file)==row['sha256'],'Changed numerical record')
            cmd=row['command'];B.require(type(cmd)is dict and set(cmd)=={'argv','returncode','timeout','elapsed_ms','stdout','stderr','stdout_sha256','stderr_sha256'},'Closed command receipt required')
            B.require(type(cmd['returncode'])is int and cmd['returncode']==0 and cmd['timeout'] is False and type(cmd['elapsed_ms'])is int and cmd['elapsed_ms']>=0,'Worker incomplete')
            argv=[runtime['python_executable'],*(['-O'] if mode=='optimized' else []),'-B',str(HERE/'source_evaluator.py'),'--_worker',case['id'],'--precision-bits',str(doc['precision_bits']),'--worker-output',str(original/row['file'])]
            B.require(B.identical(cmd['argv'],argv),'Wrong bound worker command')
            for stream in ('stdout','stderr'):
                B.require(cmd[stream]==case['id']+'.'+stream+'.log','Wrong raw log path')
                log=plain(directory/cmd[stream],root);B.require(log.stat().st_size<=65536 and B.digest(log)==cmd[stream+'_sha256'],'Changed raw log')
            value=B.strict_json(file.read_bytes());execution(value,identity,case,doc['precision_bits'],optimized=mode=='optimized')
            B.require(B.identical(value['execution']['argv'],cmd['argv'][(3 if mode=='optimized' else 2):]),'Execution record and bound command differ')
            rid=value['execution']['run_id'];B.require(rid not in runids,'Replayed execution identity');runids.add(rid)
            B.require(B.strict_json((directory/cmd['stdout']).read_bytes())=={'case':case['id'],'status':'FINITE_ENCLOSURES','run_id':rid} and not(directory/cmd['stderr']).read_bytes(),'Raw worker output mismatch')
            claims[(mode,case['id'])]=value
        reports[mode]=doc
    target=E.external(recompute_output);B.require(not target.exists() and not target.is_relative_to(root),'Independent output must be fresh outside immutable input');target.mkdir(parents=True)
    count=0;hashes={};dispositions={}
    for case in cases:
        bits=2*max(x['precision_bits'] for x in reports.values());refined=recompute_case(case,bits,target)
        execution(refined,identity,case,bits,direct=True)
        B.require(refined['execution']['run_id'] not in runids,'Checker reused producer execution')
        for mode,doc in reports.items():count+=compare_case(claims[(mode,case['id'])],refined,case,doc['precision_bits'])
        hashes[case['id']]=B.digest(target/(case['id']+'.json'));dispositions[case['id']]=scientific_disposition(refined)
    B.require(B.identical(B.source_identity(),identity),'Source changed during independent replay')
    return {'schema':'OPICA4_SOURCE_NUMERICS_LANE_V1','status':PASS_STATUS if require_clean else 'DEVELOPMENT_RECOMPUTED_FINITE_SOURCE',
      'acceptance_eligible':bool(require_clean and identity['clean']),'checked_commit':identity['head'],'checked_tree':identity['tree'],
      'source_identity':identity,'modes':['normal','optimized'],'case_ids':E.EXPECTED_IDS,'independently_recomputed_cases':len(cases),
      'contained_interval_comparisons':count,'direct_case_sha256':hashes,'dispositions':dispositions,'recompute_directory':str(target),
      'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,'kernel_or_cell_authority':False,
      'identity_ball_checks':'CONSISTENCY_ONLY_EXISTING_LEAN_IDENTITIES_RETAIN_THEOREM_AUTHORITY',**B.CAPS}
