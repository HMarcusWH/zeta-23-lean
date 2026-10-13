"""Evidence integrity mutations; fixtures are validator controls, never proofs."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from output_contract_check import release_gaps

def fixture():
    tree = 'a' * 40
    text = 'MOCK_COMPILER_TYPE_FOR_VALIDATOR_CONTROL'
    manifest = {'claim_cap':'RH_OPEN','new_lean_modules':[
        {'id':'FIXTURE','mandatory_core':True,'proposed_exports':['Mock.producer'],'status':'COMPLETE_VERIFIED'}]}
    formal = {'source_tree':tree,'independent_assumption_review_pass':True,'declarations':[
        {'theorem':'Mock.producer','authority':'PROVED','source_tree':tree,'axiom_audit_pass':True,
         'normalized_type':text,'normalized_type_sha256':hashlib.sha256(text.encode()).hexdigest()}]}
    d2 = {'status':'D2_COMPLETE','complete_layers':30,'independent_nonpartial_verified':True,
          'both_parities':True,'physical_seams_verified':True,'unresolved_tiles':0,
          'unrun_tiles':0,'missing_artifacts':0,'unverified_tiles':0,'nonfinite_enclosures':0}
    jobs = [{'name':'Mock required job','required':True,'head_tree':tree,'status':'completed',
             'conclusion':'success','scientific_acceptance':True}]
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
    return {'execution_status':'SUCCESS','integrity_status':'PASS','claim_cap':'RH_OPEN',
            'scientific_disposition':'EVIDENCE_MUTATIONS_REJECTED','rejected':rejected,
            'authority':'VALIDATOR_CONTROL_ONLY','scope':'Synthetic receipt fixtures; no theorem or D2 authority.'}

if __name__ == '__main__':
    result = run()
    out = Path(__file__).parent / 'evidence/output_mutations.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
