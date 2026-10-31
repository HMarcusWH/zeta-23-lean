from copy import deepcopy
import unittest
from research.RHRC.ffbbp.opica_composition import (
    verify_required_gates, assess_composition_reduction, restore_full_contract,
    validate_residual_budget, verify_countermodel, deduplicate_evidence_origins,
    build_falsifier_requirements)
from research.RHRC.integration.opica_composition.canonical import ContractError

class AssuranceTests(unittest.TestCase):
    def gates(self):
        req=[{'id':x,'scope':'SYNTHETIC_FIXTURE','identity':{'source':'a'*64,'run_id':'fixture','attempt':1},'checker':'fixture-replay'} for x in ('source','witness')]
        got=[{**r,'status':'PASS','evidence':['b'*64]} for r in req]
        return req,got
    def replay(self,wanted,got):
        return got['evidence']==['b'*64]
    def residual(self):
        r={'source':'a'*64,'object':'canonicalWeil','norm':'physicalL2','domain':'L>0',
           'normalization':'canonical','full_output':True,'tail':'included','quantifiers':['forall L','exists K'],
           'correction':'complete','prime_powers':[2,3,4]}
        return r,{**r,'scope':'FINITE_CERTIFICATE','exact_kernel':False}
    def test_t31(self):
        with self.assertRaises(ContractError):verify_required_gates([],[],self.replay)
    def test_t32(self):
        r,g=self.gates()
        with self.assertRaises(ContractError):verify_required_gates(r,g[:1],self.replay)
    def test_t33(self):
        r,g=self.gates();g[0]['status']='NOT_APPLICABLE'
        with self.assertRaises(ContractError):verify_required_gates(r,g,self.replay)
    def test_t34(self):
        r,g=self.gates();g[0]['status']='NOT_EVALUATED'
        with self.assertRaises(ContractError):verify_required_gates(r,g,self.replay)
    def test_t35(self):
        r,g=self.gates();g[0]=deepcopy(g[0]);g[0]['identity']['run_id']='other'
        with self.assertRaises(ContractError):verify_required_gates(r,g,self.replay)
    def test_t36(self):
        population=[{'id':'a','module':'same','context':'K=3'},{'id':'b','module':'same','context':'K=4'}]
        out=assess_composition_reduction(population,('module',),lambda r:r['context'])
        self.assertEqual(out['status'],'FALSIFIED_SUFFICIENCY');self.assertEqual(len(out['colliding_fibers']),1)
    def test_t37(self):
        full={'x':{'id':'x','module':'m','witness':{'physical':'actual','K':4}}}
        restored=restore_full_contract('x',full);self.assertEqual(restored,full['x'])
        restored['witness']['K']=5;self.assertEqual(full['x']['witness']['K'],4)
    def test_t38(self):
        r,e=self.residual();e['norm']='different'
        with self.assertRaises(ContractError):validate_residual_budget(r,e,lambda *_:True)
    def test_t39(self):
        r,e=self.residual();e['exact_kernel']=True
        with self.assertRaises(ContractError):validate_residual_budget(r,e,lambda *_:True)
    def test_t40(self):
        r,e=self.residual();e['object']='causalGram'
        with self.assertRaises(ContractError):validate_residual_budget(r,e,lambda *_:True)
    def test_t41(self):
        t={'premises':['Hermitian','sameSource'],'source_kind':'ACTUAL_ZETA'}
        m={'preserved_premises':['Hermitian'],'source_kind':'SYNTHETIC_CONTROL'}
        with self.assertRaises(ContractError):verify_countermodel(t,m,lambda *_:True)
    def test_t42(self):
        r,e=self.residual();e['prime_powers']=[2,3]
        with self.assertRaises(ContractError):validate_residual_budget(r,e,lambda *_:True)
    def test_t43(self):
        rows=[{'source':'a'*64,'invocation':'one','raw_sha256':'b'*64,'framework':f} for f in ('FFBBP','OoL','Permansson')]
        self.assertEqual(len(deduplicate_evidence_origins(rows)),1)
    def test_t44(self):
        r,g=self.gates();r[0]['scope']=g[0]['scope']='PRIVATE_N29'
        with self.assertRaises(ContractError):verify_required_gates(r,g,self.replay)
    def test_t81(self):self.test_t31()
    def test_t82(self):self.test_t32()
    def test_complete_positive_and_replay_rejection(self):
        r,g=self.gates();self.assertEqual(verify_required_gates(r,g,self.replay),('source','witness'))
        with self.assertRaises(ContractError):verify_required_gates(r,g,lambda *_:False)
    def test_native_nonunit_witness_is_legal(self):
        controls=build_falsifier_requirements({'newborn':True,'shell_unit':True,'witness_nonzero':True})
        self.assertNotIn('ADAPTER_REQUIRED_UNIT_WITNESS',controls)
    def test_reduction_gold_leakage(self):
        with self.assertRaises(ContractError):assess_composition_reduction([],('gold',),lambda _:True)

if __name__=='__main__':unittest.main()
