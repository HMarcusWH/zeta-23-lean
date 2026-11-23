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
    from research.RHRC.integration.opica_composition.inventory import expression_hash
    for row in record["targets"]:
      dag=row["expected_expression"]
      self.assertEqual(set(dag),{"format","root","nodes"})
      self.assertEqual(dag["format"],"LEAN_EXPR_DAG_V1")
      self.assertEqual(len(expression_hash(dag)),64)
  def test_static_source_scope(self):
    a=s.check()
    self.assertEqual(a["status"],"PASS_ADDITIVE_SOURCE_BYTES_ONLY")
    self.assertFalse(a["proof_acceptance"])
if __name__=="__main__":unittest.main()
