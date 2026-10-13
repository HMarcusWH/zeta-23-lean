"""Evidence integrity mutations; fixtures are validator controls, never proofs."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from output_contract_check import release_gaps,frozen_spec,FORMAL_JOB,REGRESSION_JOB,NATIVE_JOB,RESEARCH_JOBS

def fixture():
    tree = 'a' * 40
    text = 'MOCK_COMPILER_TYPE_FOR_VALIDATOR_CONTROL'
    manifest = frozen_spec()
    for module in manifest['new_lean_modules']:module['status']='COMPLETE_VERIFIED'
    for package in manifest['work_packages']:package['status']='COMPLETE_VERIFIED'
    declarations=[{'theorem':name,'authority':'PROVED','source_tree':tree,'axiom_audit_pass':True,'axioms':[],
         'normalized_type':text,'normalized_type_sha256':hashlib.sha256(text.encode()).hexdigest()} for module in manifest['new_lean_modules'] for name in module['proposed_exports']]
    formal = {'source_tree':tree,'head':'c'*40,'compiler_context':{'head':'c'*40,'tree':tree},'execution_status':'SUCCESS','integrity_status':'PASS','claim_cap':'RH_OPEN','producer_complete':True,'independent_assumption_review_pass':True,'declarations':declarations}
    d2 = {'status':'D2_COMPLETE','complete_layers':30,'independent_nonpartial_verified':True,
          'both_parities':True,'physical_seams_verified':True,'unresolved_tiles':0,
          'unrun_tiles':0,'missing_artifacts':0,'unverified_tiles':0,'nonfinite_enclosures':0}
    jobs = [{'workflow':workflow,'name':name,'required':True,'head':'c'*40,'head_tree':tree,'status':'completed',
             'conclusion':'success','scientific_acceptance':True} for workflow,name in [FORMAL_JOB,REGRESSION_JOB,sorted(RESEARCH_JOBS)[0],NATIVE_JOB]]
    jobs[-1]['native_output_review']={'head':'c'*40,'source_tree':tree,'scope':'FINITE_FIXED_PROBES','frozen_panel_complete':True,'pair_count':44,'row_count':176,'evaluated_rows':176,'unresolved_rows':0,'verified_pairs':44,'unresolved_pairs':0,'universal_theorem_authority':False}
    for job in jobs:
        job['classification']='FORMAL_VALIDITY_GATE' if job['name']=='lean-components' else 'REGRESSION_GATE' if job['name']=='exact-controls' else 'RESEARCH_PRODUCING_CHECK'
        job['output_reviewed']=True
    return [manifest,formal,d2,jobs]

def run():
    controls = fixture()
    assert not release_gaps(*controls)
    rejected = []
    def mutation(name, change):
        args = deepcopy(controls)
        change(args)
        assert release_gaps(*args), name
        rejected.append(name)
    mutation('stale theorem type',lambda a:a[1]['declarations'][0].update(normalized_type='changed'))
    mutation('wrong compiler tree',lambda a:a[1]['declarations'][0].update(source_tree='b'*40))
    mutation('generic interface as producer',lambda a:a[1]['declarations'][0].update(authority='PAPER'))
    mutation('missing branch producer',lambda a:a[0]['new_lean_modules'][0]['proposed_exports'].append('Mock.odd'))
    mutation('unresolved D2 marked complete',lambda a:a[2].update(unresolved_tiles=1))
    mutation('pointwise cover as intervals',lambda a:a[2].update(independent_nonpartial_verified=False))
    mutation('missing D2 layer',lambda a:a[2].update(complete_layers=29))
    mutation('nonfinite enclosure dropped',lambda a:a[2].update(nonfinite_enclosures=1))
    mutation('skipped required job passed',lambda a:a[3][0].update(conclusion='skipped'))
    mutation('running required job passed',lambda a:a[3][0].update(status='in_progress'))
    mutation('assumption review omitted',lambda a:a[1].update(independent_assumption_review_pass=False))
    mutation('module scope silently narrowed',lambda a:a[0]['new_lean_modules'][0].update(status='PARTIAL'))
    mutation('empty core scope vacuity',lambda a:a[0].update(new_lean_modules=[]))
    mutation('mandatory core demoted',lambda a:a[0]['new_lean_modules'][0].update(mandatory_core=False))
    mutation('mandatory export inventory removed',lambda a:a[0]['new_lean_modules'][0].update(proposed_exports=[]))
    mutation('duplicate compiler declaration',lambda a:a[1]['declarations'].append(deepcopy(a[1]['declarations'][0])))
    mutation('component receipt as full producer',lambda a:a[1].update(producer_complete=False))
    mutation('required job demoted',lambda a:a[3][0].update(required=False))
    mutation('required formal job missing',lambda a:a[3].pop(0))
    mutation('raw harvest schema used as approval',lambda a:a[3][0].pop('required'))
    mutation('unadmitted proof axiom',lambda a:a[1]['declarations'][0].update(axioms=['sorryAx']))
    mutation('wrong job head',lambda a:a[3][0].update(head='d'*40))
    mutation('mandatory work package demoted',lambda a:a[0]['work_packages'][0].update(mandatory=False))
    mutation('native W10 scope left partial',lambda a:a[0]['work_packages'][-1].update(status='PARTIAL'))
    mutation('compiler context missing',lambda a:a[1].pop('compiler_context'))
    mutation('native observation job missing',lambda a:a[3].pop())
    mutation('native incomplete row coverage',lambda a:a[3][-1]['native_output_review'].update(row_count=172))
    mutation('native unresolved rows hidden',lambda a:a[3][-1]['native_output_review'].update(unresolved_rows=1))
    mutation('native observation as universal theorem',lambda a:a[3][-1]['native_output_review'].update(universal_theorem_authority=True))
    mutation('native checked at different source tree',lambda a:a[3][-1]['native_output_review'].update(source_tree='b'*40))
    mutation('unknown workflow silently ignored',lambda a:a[3].append({'workflow':'Unknown workflow','name':'unknown','required':False,'head':'c'*40,'head_tree':'a'*40,'status':'completed','conclusion':'success','scientific_acceptance':False,'classification':'REQUIRES_SOURCE_REVIEW','output_reviewed':False}))
    mutation('job classified without reading outputs',lambda a:a[3][0].update(output_reviewed=False))
    mutation('missing job classification',lambda a:a[3][0].pop('classification'))
    return {'execution_status':'SUCCESS','integrity_status':'PASS','claim_cap':'RH_OPEN',
            'scientific_disposition':'EVIDENCE_MUTATIONS_REJECTED','rejected':rejected,
            'authority':'VALIDATOR_CONTROL_ONLY','scope':'Synthetic receipt fixtures; no theorem or D2 authority.'}

if __name__ == '__main__':
    result = run()
    out = Path(__file__).parent / 'evidence/output_mutations.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
