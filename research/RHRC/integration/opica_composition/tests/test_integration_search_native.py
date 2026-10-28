"""Three actual, non-calibration compositions; complete answers withheld."""
import functools
import unittest
from research.RHRC.integration.opica_composition.canonical import require,load_bytes
from research.RHRC.integration.opica_composition.contracts import StatementInventory,GrammarProfile,SearchBudget,CompositionProposal
from research.RHRC.integration.opica_composition.inventory import expression_hash
from research.RHRC.integration.opica_composition.qualification import atlas_driver
from research.RHRC.integration.opica_composition.executor import run_worker,execute_attempt,lean_name
from research.RHRC.integration.opica_composition.proposals import enumerate_candidates,used_constant_ids
from research.RHRC.integration.opica_composition.service import _target,_search_contract
from research.RHRC.integration.opica_composition.tests.test_executor import native_context,fresh,independently_verify,REPO

TARGETS=('INTEGRATION_CLOSURE','INTEGRATION_SOURCE','INTEGRATION_INDEX')


@functools.lru_cache(None)
def fresh_contracts():
    worker,snapshot,_=native_context()
    doc=load_bytes((REPO/'research/RHRC/integration/opica_composition/SEARCH_CONTRACTS.json').read_bytes())
    require(doc['kernel_acceptance'] is False and [r['target_id'] for r in doc['targets']]==list(TARGETS),
            'Reviewed retrieval target census differs')
    rows=doc['statements'];require(len(rows)==6 and len({r['declaration'] for r in rows})==6,'Reviewed six-link census differs')
    text=atlas_driver(rows)
    for row in rows:
        text+='\nrun_cmd Zeta23.RHRC.OpicaComposition.exportRetrievalProofConstants `'+lean_name(row['declaration'])+' "type"\n'
    for tid in TARGETS:
        target,_=_target(REPO,snapshot,tid)
        text+='\nrun_cmd Zeta23.RHRC.OpicaComposition.exportTarget `'+lean_name(target.declaration)+' "value"\n'
        text+='run_cmd Zeta23.RHRC.OpicaComposition.exportRetrievalProofConstants `'+lean_name(target.declaration)+' "value"\n'
    folder=fresh('actual-search-contracts');folder.mkdir()
    (folder/'Contracts.lean').write_text('import Zeta23.OPICARound4.IntegrationTargets\nimport Zeta23.RHRC.OpicaComposition.Export\n'+text,encoding='utf8')
    built=run_worker(worker,folder,'Contracts.lean','Contracts.olean',SearchBudget(**(worker.budget or {})))
    require(built['exit_code']==0 and built['resource_status'] is None,'Fresh retrieval contract export failed')
    exported={};proofs=[];targets=[]
    for line in (folder/'Contracts.lean.log').read_bytes().splitlines():
        if line.startswith(b'OPICA3_ATLAS\t'):
            r=load_bytes(line.split(b'\t',1)[1]);exported[r['declaration']]=r
        elif line.startswith(b'OPICA_RETRIEVAL_PROOFS\t'):proofs.append(load_bytes(line.split(b'\t',1)[1]))
        elif line.startswith(b'OPICA_TARGET\t'):targets.append(load_bytes(line.split(b'\t',1)[1]))
    require(len(exported)==6 and len(proofs)==9 and len(targets)==3,'Incomplete fresh contract export')
    for i,row in enumerate(rows):
        actual=exported[row['declaration']]
        require(actual['type_expression']==row['type_expression'] and actual['module']==row['module'] and
                expression_hash(actual['type_expression'])==row['type_sha256'] and
                proofs[i]==row['proof_constants'] and set(actual['axioms'])<={'propext','Classical.choice','Quot.sound'},
                'Retrieval statement differs from fresh full compiler type')
    for i,row in enumerate(doc['targets']):
        target,_=_target(REPO,snapshot,row['target_id'])
        require(targets[i]==row['expected_expression'] and expression_hash(targets[i])==target.expected_type_hash and
                proofs[6+i]==row['proof_constants'],'Retrieval target differs from fresh compiler type')
    return doc


class NativeIntegrationSearchTests(unittest.TestCase):
    def prove(self,tid):
        doc=fresh_contracts();worker,snapshot,_=native_context();target,table=_target(REPO,snapshot,tid)
        inventory=StatementInventory(snapshot.generation,[],'a'*64)
        batch=enumerate_candidates(inventory,target,GrammarProfile([],[]),SearchBudget(**(worker.budget or {})),
            search_contract=_search_contract(REPO,target))
        retrieved=[r for r in batch.candidates if r.get('scientific_scope')=='BOUNDED_TARGET_DIRECTED_RETRIEVAL_NOT_PROOF']
        self.assertTrue(retrieved,'No actual native multi-step candidate '+tid)
        row=retrieved[0]
        self.assertEqual(len(used_constant_ids(row['term_plan'])),2,'Complete-answer or one-link shortcut')
        self.assertFalse(row['search_provenance']['kernel_acceptance'])
        proposal=CompositionProposal(row['action_id'],tid,snapshot.generation,row['term_plan'])
        result=execute_attempt(proposal,target,snapshot,fresh('actual-search-attempt'),worker=worker,constant_table=table)
        self.assertEqual(result.status,'PROVED_CONDITIONAL',result.reason+' '+result.output)
        self.assertEqual(independently_verify(result,target).status,'PROVED_CONDITIONAL')

    def test_actual_eventual_closure_chain(self):self.prove(TARGETS[0])
    def test_actual_complete_signed_source_budget_chain(self):self.prove(TARGETS[1])
    def test_actual_physical_joint_index_chain(self):self.prove(TARGETS[2])


if __name__=='__main__':unittest.main()
