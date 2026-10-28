import unittest
from research.RHRC.integration.opica_composition.closure import evaluate_closure
from research.RHRC.integration.opica_composition.canonical import ContractError

class ClosureTests(unittest.TestCase):
    def leaf(self,key,proof=None):return {'id':key,'kind':'LEAF','proposition':key,'source':'actual','witness':'same',
        'quantifiers':['forall L'],'consumers':[],'status':'OPEN','next_test':'source budget','proof_evidence':proof}
    def test_one_route_suffices_but_all_its_premises_required(self):
        n=[self.leaf('a','p'),self.leaf('b'),self.leaf('c','q'),{'id':'ab','kind':'AND','children':['a','b']},
            {'id':'root','kind':'OR','children':['ab','c']}]
        self.assertEqual(evaluate_closure(n,'root',verified_leaves={'a':'p'})['status'],'OPEN')
        self.assertEqual(evaluate_closure(n,'root',verified_leaves={'c':'q'})['status'],'PROVED')
        self.assertEqual(evaluate_closure(n,'root',verified_leaves={'c':'q'})['RH'],'OPEN')
    def test_open_field_does_not_supply_a_proof(self):
        n=[self.leaf('a')];n[0]['status']='PROVED'
        self.assertEqual(evaluate_closure(n,'a',verified_leaves={})['status'],'OPEN')
    def test_cycles_rejected(self):
        with self.assertRaises(ContractError):evaluate_closure([{'id':'a','kind':'AND','children':['a']}],'a',verified_leaves={})

if __name__=='__main__':unittest.main()
