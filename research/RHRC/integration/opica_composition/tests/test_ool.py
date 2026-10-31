from copy import deepcopy
import unittest
from research.RHRC.ool.opica_composition import verify_interfaces,check_phase,search_disposition,validate_route
from research.RHRC.integration.opica_composition.canonical import ContractError

class RouteTests(unittest.TestCase):
    def route(self):
        req=[{'id':str(i),'source':'a'*64,'context':'b'*64,'producer':'x','consumer':'x',
              'witness':'physicalW','phase':'CONFIRMATORY_FROZEN'} for i in range(5)]
        actual=[{**r,'observed_phase':'CONFIRMATORY_FROZEN','receipt':'c'*64,'transport':None} for r in req]
        return req,actual
    def replay(self,req,row):return row['receipt']=='c'*64
    def test_t45(self):
        r,g=self.route()
        with self.assertRaises(ContractError):verify_interfaces(r,g[:1],self.replay)
    def test_t46(self):
        r,g=self.route();g[0]['receipt']=None;g[0]['actual_output_bound']=True
        with self.assertRaises(ContractError):verify_interfaces(r,g,self.replay)
    def test_t47(self):
        r,g=self.route()
        with self.assertRaises(ContractError):verify_interfaces(r,g,lambda *_:False)
    def test_t48(self):
        self.assertEqual(search_disposition(complete=False,exhausted=False,proved=False),'UNRESOLVED_INVENTORY')
    def test_t49(self):
        r,g=self.route();g[1]['id']=g[0]['id']
        with self.assertRaises(ContractError):verify_interfaces(r,g,self.replay)
    def test_t50(self):
        r,g=self.route();g[0]['observed_phase']='DISCOVERY'
        with self.assertRaises(ContractError):verify_interfaces(r,g,self.replay)
    def test_t83(self):self.test_t49()
    def test_t84(self):
        with self.assertRaises(ContractError):check_phase('CONFIRMATORY_FROZEN','DISCOVERY')
    def test_positive_complete_route(self):
        r,g=self.route();self.assertEqual(len(verify_interfaces(r,g,self.replay)),5)
    def test_cyclic_proof_rejected(self):
        with self.assertRaises(ContractError):validate_route([{'id':'a','inputs':['b']},{'id':'b','inputs':['a']}],frozenset({'a','b'}))
    def test_transport_needs_checked_receipt(self):
        r,g=self.route();r[0]['consumer']=g[0]['consumer']='y'
        with self.assertRaises(ContractError):verify_interfaces(r,g,self.replay)

if __name__=='__main__':unittest.main()
