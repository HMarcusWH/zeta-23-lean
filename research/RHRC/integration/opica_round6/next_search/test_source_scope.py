import json
from pathlib import Path
import unittest
import source_scope as s
class NextArithmeticSourceScopeTests(unittest.TestCase):
  def test_no_old_11_lane_promotion(self):
    self.assertEqual(s.BASE,"bb7c8184a135b2823c6296917c5ac893bebf2a71")
    self.assertEqual(len(s.NEW),11)
    self.assertNotIn("research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json",s.NEW)
    self.assertIn("research/RHRC/integration/opica_composition/PUBLIC_TARGETS.json",s.FROZEN)
  def test_exact_open_research_target_ids(self):
    t=json.loads((Path(__file__).resolve().parent/"TARGETS.json").read_text())
    self.assertEqual(t["claims"],{"RH":"OPEN","C1":"OPEN"})
    self.assertEqual([x["id"] for x in t["targets"]],[
      "DIRECT_SIGNED_SHELL_POSITIVE","DIRECT_SIGNED_SHELL_NEGATIVE",
      "ONE_POLARITY_SHELL_SUBPOWER","P303_OPPOSED_PRODUCT_UPPER",
      "N20_JOINT_ARITHMETIC_UPPER","PAPER_ROUTE_VALIDATION"])
    self.assertTrue(all(x["status"]=="OPEN" for x in t["targets"]))
    self.assertEqual(t["approved_independent_proof_constants"],[])
  def test_no_renamed_terminal_or_silent_source_substitute(self):
    t=json.loads((Path(__file__).resolve().parent/"TARGETS.json").read_text())
    self.assertTrue(all(x["exact_original"] is False for x in t["targets"] if x.get("lean")))
    self.assertTrue(any("riemannHypothesis" in x for x in t["forbidden"]))
  def test_falsifiers_complete(self):
    d=json.loads((Path(__file__).resolve().parent/"FALSIFIERS.json").read_text())
    names={x["id"] for x in d["tests"]}
    self.assertTrue({"COMPLETE_SHELL","SPENT_PARTNERS","FIXED_POLARITY",
                     "PHYSICAL_WEIGHTS","CIRCULARITY"}.issubset(names))
  def test_lean_proof_fragment_no_placeholder(self):
    code=(s.REPO/"Zeta23/OPICARound6/NextSearch/SourceEnergies.lean").read_text()
    for bad in ("\naxiom ","\nsorry","\nby sorry","native_decide", "_root_.riemannHypothesis"):
      self.assertNotIn(bad,code)
    self.assertIn("NativeFullTransfer.native_raw_energy_upper",code)
  def test_subpower_constants_before_horizon(self):
    code=(s.REPO/"Zeta23/OPICARound6/NextSearch/SourceEnergies.lean").read_text()
    self.assertEqual(code.count("0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X₀ : ℕ"),2)
    self.assertIn("max X₀ 64 ≤ X",code)
    self.assertIn("C * (X : ℝ)^ε",code)
  def test_compiler_expression_dag_is_object_not_string(self):
    # Lean's Export.exportTarget emits OPICA_TARGET followed by compact JSON
    # with root/nodes. The original structured DAG cannot be treated as a
    # plain string; malformed objects fail the existing expression validator.
    code=(s.REPO/"research/RHRC/integration/opica_round6/next_search/typed_export.py").read_text()
    self.assertIn('type(expression) is not dict',code)
    self.assertIn('set(expression) != {"format","root","nodes"}',code)
    self.assertIn('expression_hash(expression)',code)
    self.assertNotIn('isinstance(expression,str)',code)
  def test_frozen_native_dag_has_full_compiler_schema(self):
    # Real historical original OPICA compiler exports, not a mocked string.
    record=json.loads((s.REPO/"research/RHRC/integration/opica_composition/SEARCH_CONTRACTS.json").read_text())
    import sys
    if str(s.REPO) not in sys.path: sys.path.insert(0,str(s.REPO))
    from research.RHRC.integration.opica_composition.inventory import expression_hash
    for row in record["targets"]:
      dag=row["expected_expression"]
      self.assertEqual(set(dag),{"format","root","nodes"})
      self.assertEqual(dag["format"],"LEAN_EXPR_DAG_V1")
      self.assertEqual(len(expression_hash(dag)),64)
  def test_actual_atlas_exporter_is_in_compiler_dependency_set(self):
    workflow=(s.REPO/".github/workflows/opica-next-arithmetic.yml").read_text()
    self.assertIn("lake build Zeta23.RHRC.OpicaRound3AtlasExport",workflow)
    self.assertIn("lake build Zeta23.RHRC.OpicaComposition.Export",workflow)
    self.assertIn("Run actual original OPICA typed-DAG backward source search",workflow)
  def test_compiler_dag_statement_inventory_native_json_roundtrip(self):
    # Exercise the exact validation boundary from the search job that failed
    # at head 853a808e. Use a *real frozen native Lean expression DAG* rather
    # than a handwritten fake type hash. No proof claim is made by this test.
    import sys
    if str(s.REPO) not in sys.path: sys.path.insert(0,str(s.REPO))
    from research.RHRC.integration.opica_composition.canonical import ContractError
    from research.RHRC.integration.opica_composition.contracts import (
        StatementContract, StatementInventory)
    from research.RHRC.integration.opica_composition.inventory import expression_hash

    archive=json.loads((s.REPO/"research/RHRC/integration/opica_composition/SEARCH_CONTRACTS.json").read_text())
    prior=archive["statements"][0]
    dag=prior["type_expression"]
    binders=[]
    cursor=int(dag["root"])
    while True:
      node=dag["nodes"][cursor]
      if node[0]=="mdata":
        cursor=int(node[2])
        continue
      if node[0]!="forall": break
      info=node[2]
      binders.append({"position":len(binders),"name":"frozenCompilerBinder",
                      "binder_info":info,"domain_text":"frozen compiler domain",
                      "domain_is_prop":False,
                      "typeclass_binder":info=="instImplicit",
                      "class_name":None})
      cursor=int(node[4])
    typed=StatementContract(
        declaration=prior["declaration"],module=prior["module"],
        type_expression=dag,type_sha256=expression_hash(dag),
        universe_parameters=[],outer_telescope=binders,
        conclusion_text="frozen native DAG codec fixture",
        type_constants=[],value_constants=[],axioms=[])
    generation="0"*64
    export_hash="1"*64
    # The old bug was feeding dataclass instances straight into this codec.
    with self.assertRaises(ContractError):
      StatementInventory(generation,[typed],export_hash)
    sealed=StatementInventory(generation,[typed.to_dict()],export_hash)
    restored=StatementInventory.from_bytes(sealed.to_bytes())
    self.assertEqual(restored.to_bytes(),sealed.to_bytes())
    self.assertEqual(restored.digest,sealed.digest)
    self.assertEqual(restored.statements[0]["type_sha256"],typed.type_sha256)
    campaign=(s.REPO/"research/RHRC/integration/opica_round6/next_search/campaign.py").read_text()
    self.assertIn("[record.to_dict() for record in typed]",campaign)
  def test_seed_constants_do_not_count_as_new_proofs(self):
    from campaign import classify_unverified_proposals
    seed=lambda ident: {
        "status":"PROPOSED_NOT_KERNEL_CHECKED",
        "action_id":ident,
        "term_plan":{"tag":"const","constant_id":ident},
        "kernel_acceptance":False}
    seeds=[seed("source-a"),seed("source-b")]
    seen=classify_unverified_proposals(seeds)
    self.assertEqual(seen["schema"],"OPICA_NEXT_SOURCE_CANDIDATE_COUNTS_V2")
    self.assertEqual(seen["bare_approved_source_constant_seeds"],2)
    self.assertEqual(seen["unverified_nontrivial_composition_plans"],0)
    self.assertEqual(seen["kernel_accepted_target_proofs"],0)
    self.assertEqual(seen["research_disposition"],"SEED_ONLY_NO_NEW_COMPOSITION")
    nontrivial={**seed("plan-1"),
                "term_plan":{"tag":"app","function":{"tag":"const",
                              "constant_id":"source-a"},"arguments":[]}}
    combined=classify_unverified_proposals(seeds+[nontrivial])
    self.assertEqual(combined["unverified_nontrivial_composition_plans"],1)
    self.assertEqual(combined["kernel_accepted_target_proofs"],0)
    self.assertEqual(combined["research_disposition"],"UNVERIFIED_COMPOSITION_PLANS_PRESENT")
    rejected={"status":"REJECTED_UNAPPROVED_CONSTANT",
              "action_id":"forbidden","kernel_acceptance":False}
    self.assertEqual(classify_unverified_proposals(seeds+[rejected])["rejected_before_kernel"],1)
    with self.assertRaises(ValueError):
      classify_unverified_proposals(seeds+[{**seed("forged"),"kernel_acceptance":True}])
    with self.assertRaises(ValueError):
      classify_unverified_proposals(seeds+[{"status":"PROVED","kernel_acceptance":False}])

  def test_static_source_scope(self):
    a=s.check()
    self.assertIn(a["status"],{"PASS_ADDITIVE_SOURCE_BYTES_ONLY",
                                "PASS_REVIEWED_COMBINED_EPOCH_V1"})
    self.assertFalse(a["proof_acceptance"])
if __name__=="__main__":unittest.main()
