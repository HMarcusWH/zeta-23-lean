import unittest
from research.RHRC.integration.opica_composition.canonical import (
    ContractError, digest_text, relative_path, validate_path_inventory, load_bytes)
from research.RHRC.integration.opica_composition.contracts import CompositionProposal, SearchBudget

LANES=("CONTRACT","PARENT_REGRESSION","CURRENT_COMPATIBILITY","COMPOSITION_FORMAL",
       "SEMANTIC_NEGATIVES","FRAMEWORK_ADAPTERS","PROVIDER_SELECTED","REPLAY_CAMPAIGN","GENERATED_STATE","ACCEPTANCE")

class ContractCases(unittest.TestCase):
    def test_t104(self):
        # IDs are exact identities, not presentation aliases.
        from research.RHRC.integration.opica_composition.contracts import validate_lane_id
        self.assertEqual(validate_lane_id("PARENT_REGRESSION"),"PARENT_REGRESSION")
        for alias in ("parent_regression","PARENT","PARENT-REGRESSION"," PARENT_REGRESSION"):
            with self.assertRaises(ContractError): validate_lane_id(alias)

    def test_t109(self):
        self.assertEqual(digest_text("a"*64),"a"*64)
        for value in ("a"*64+"\n","a"*64+"\r","a"*64+" ","a"*63,"a"*65,"A"*64,"а"*64):
            with self.assertRaises(ContractError): digest_text(value)
            with self.assertRaises(ContractError): CompositionProposal("p","t",value,{"tag":"local","binder_slot":0})

    def test_t110(self):
        self.assertEqual(relative_path("Evidence/actual-result.json"),"Evidence/actual-result.json")
        for value in ("CON","foo/NUL.txt","COM1.out","a.","a ","foo~1/x","a:b","a\\b","../x"):
            with self.assertRaises(ContractError): relative_path(value)

    def test_t111(self):
        self.assertEqual(validate_path_inventory(["A/x","B/y"]),("A/x","B/y"))
        for paths in (["A/x","a/y"],["A/x","A/X"],["A","A/x"],["a/x","a/x"]):
            with self.assertRaises(ContractError): validate_path_inventory(paths)

    def test_closed_mutable_fields(self):
        plan={"tag":"local","binder_slot":0}; p=CompositionProposal("p","t","a"*64,plan)
        plan["binder_slot"]=99
        self.assertEqual(p.plan["binder_slot"],0)
        p.plan["binder_slot"]=99
        with self.assertRaises(ContractError): _=p.digest
        with self.assertRaises(ContractError): SearchBudget(term_nodes=True)
        with self.assertRaises(ContractError): load_bytes(b'{"x":1,"x":2}')
