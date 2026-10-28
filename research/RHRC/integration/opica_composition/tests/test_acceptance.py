from copy import deepcopy
from pathlib import Path
from dataclasses import replace
import tempfile,hashlib,json,unittest
from research.RHRC.integration.opica_composition.accept import (
 ROUND4_LANES,verify_gate_inventory,verify_lane_bundle,accept_application_scope,require_native_receipt,
 preserve_scientific_disposition)
from research.RHRC.integration.opica_composition.canonical import ContractError,canonical_bytes
from research.RHRC.integration.opica_composition.cache_owner import CacheWriterLease
from research.RHRC.integration.opica_composition.closure import evaluate_closure

class AcceptanceTests(unittest.TestCase):
    def setUp(self):self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
    def tearDown(self):self.tmp.cleanup()
    def lane(self,scope='CURRENT_HOST'):
        raw=b'{"fixture":"raw-regression-record"}';(self.root/'raw.json').write_bytes(raw)
        expected={'id':'CONTRACT','scope':scope,'checked':{'commit':'a'*40,'tree':'b'*40,'environment':'c'*64}}
        exp={'run_id':'fixture','attempt':1,'requested_commit':'d'*40,'requested_tree':'e'*40,'profile_digest':'f'*64}
        record={'schema':'OPICA4_LANE_BUNDLE_V1','lane_id':'CONTRACT','scope':scope,'experiment':exp,
                'checked':expected['checked'],'conclusion':'success',
                'artifacts':[{'path':'raw.json','bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}],
                'records':['raw.json']}
        self.write(record);return expected,exp,record
    def write(self,row):(self.root/'lane.json').write_bytes(canonical_bytes(row))
    def replay(self,*args):return args[2]['raw.json'].read_bytes()==b'{"fixture":"raw-regression-record"}'
    def test_t64(self):
        leaf={'id':'terminal','kind':'LEAF','proposition':'actual source signed bound','source':'actualzeta',
              'witness':'same','quantifiers':['forall L'],'consumers':[],'status':'OPEN','next_test':'joint error budget'}
        self.assertEqual(evaluate_closure([leaf],'terminal',verified_leaves={})['Step4'],'OPEN')
    def test_t65(self):
        e,x,r=self.lane();r['conclusion']='skipped';self.write(r)
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)
    def test_t66(self):
        e,x,r=self.lane()
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=x,replay=lambda *_:False)
    def test_t67(self):
        from research.RHRC.integration.opica_composition.descendant import current_compatibility_scope
        with self.assertRaises(ContractError):current_compatibility_scope({'scope':'FROZEN_BASELINE','checked_commit':'a','checked_tree':'b'},'a','b')
    def test_t68(self):
        from research.RHRC.integration.opica_composition.proposals import validate_plan
        for p in ({'tag':'shell','command':'curl https://example.invalid'}, {'tag':'const','constant_id':'a'*64,'run_cmd':'arbitrary'}):
            with self.assertRaises(ContractError):validate_plan(p)
    def test_t69(self):
        with CacheWriterLease(self.root/'cache'):
            with self.assertRaises(ValueError):
                with CacheWriterLease(self.root/'cache'):pass
        with CacheWriterLease(self.root/'cache'):pass
    def test_t70(self):
        a={'source':'same','case':'mixedresidues','scientific_status':'FALSIFIED'}
        self.assertEqual(preserve_scientific_disposition(a,a),'PRESERVED_FALSIFIED')
    def test_t71(self):
        needs={k:'success' for k in ROUND4_LANES};needs['COMPOSITION_FORMAL']='in_progress'
        with self.assertRaises(ContractError):accept_application_scope([{'id':k} for k in ROUND4_LANES],
            {k:self.root for k in ROUND4_LANES},experiment={},checkers={k:lambda *_:True for k in ROUND4_LANES},required_needs=needs)
    def test_t72(self):
        from research.RHRC.integration.opica_composition.baseline import require_unchanged
        with self.assertRaises(ContractError):require_unchanged(b'old provider authority',b'new erases old','FRAMEWORK_REGISTRY.json')
    def test_t87(self):
        e,x,r=self.lane('SELECTED_PROVIDER')
        self.assertNotEqual(e['checked']['commit'],x['requested_commit'])
        self.assertEqual(verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)['scope'],'SELECTED_PROVIDER')
    def test_t88(self):
        e,x,r=self.lane();self.assertEqual(verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)['id'],'CONTRACT')
        y={**x,'attempt':2}
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=y,replay=self.replay)
    def test_t94(self):
        from research.RHRC.integration.opica_composition.descendant import validate_classification_extension,exact_rule
        base={'rules':[{'id':'original','pattern':'original'}]};new=exact_rule('new',['exact.py'],'RESEARCH_EXECUTABLE','AUDIT_ONLY')
        with self.assertRaises(ContractError):validate_classification_extension({'rules':[new]},base,[new])
    def test_t97(self):
        from research.RHRC.integration.opica_composition.contracts import WorkerConfig
        from research.RHRC.integration.opica_composition.executor import worker_capability
        w=WorkerConfig(str(self.root/'MISSINGLEAN'),str(self.root),[str(self.root)],production=False)
        with self.assertRaises(ContractError):worker_capability(w)
    def test_t98(self):
        (self.root/'Uncompiled.lean.in').write_text('example : True := True.intro')
        with self.assertRaises(ContractError):require_native_receipt({'exit_code':0,'native_executed':False,'compiled_object':None})
    def test_t100(self):
        from research.RHRC.integration.opica_composition.historical import preserve_dispositions
        original=[{'id':str(i),'status':'OPEN' if i%2 else 'FALSIFIED'} for i in range(17)]
        with self.assertRaises(ContractError):preserve_dispositions(original,[{'id':str(i),'status':'PROVED'} for i in range(17)])
    def test_t105(self):
        for ids in ([*ROUND4_LANES,'ACCEPTANCE'],list(ROUND4_LANES)[1:]):
            with self.assertRaises(ContractError):verify_gate_inventory(ids)
    def test_t115(self):
        with self.assertRaises(ContractError):verify_gate_inventory(['contract','runtime-regressions','current-formal','source-evaluator'])
    def test_raw_file_mutation_rejected(self):
        e,x,r=self.lane();(self.root/'raw.json').write_bytes(b'forged')
        with self.assertRaises(ContractError):verify_lane_bundle(e,self.root,experiment=x,replay=self.replay)

if __name__=='__main__':unittest.main()
