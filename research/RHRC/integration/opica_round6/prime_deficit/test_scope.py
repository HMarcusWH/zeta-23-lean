import json
from pathlib import Path
import unittest
import scope
class SourceContractTests(unittest.TestCase):
  def test_exact_source_contract(self):
    p=Path(__file__).resolve().parent/"SOURCE_CONTRACT.json"
    c=json.loads(p.read_text())
    self.assertEqual(c["source_base_head"],scope.BASE)
    self.assertEqual(c["open_goals"],[
      "LargePrimeDeficitSubpower","MissingPrimeDeficitToLiteralGBridge"])
    self.assertEqual(c["conditional_transfer_status"],"OPEN_NOT_COMPILED_OR_PROVED")
    self.assertFalse(c["proof_acceptance"])
  def test_no_center_omission_or_window_rewrite(self):
    x=(scope.REPO/"Zeta23/OPICARound6/PrimeDeficit/Source.lean").read_text()
    for t in ("smallPrimeCenter N","Nat.primesLE","⌊(K:ℝ)^((3:ℝ)/2)⌋₊",
              "Real.eulerMascheroniConstant","primeFractionalPart N p"):
      self.assertIn(t,x)
    for t in ("\naxiom ","\nsorry","by sorry","_root_.riemannHypothesis"):
      self.assertNotIn(t,x)
  def test_adversarial_claim_and_math_mutations(self):
    # This suite runs both normally and with python -O; all rejection logic
    # must survive interpreter optimization.
    contract=json.loads((Path(__file__).resolve().parent/"SOURCE_CONTRACT.json").read_text())
    source=(scope.REPO/"Zeta23/OPICARound6/PrimeDeficit/Source.lean").read_text()
    scope.validate_semantics(contract,source)
    for field,value in (("RH","PROVED"),("Step4","CLOSED"),
                        ("proof_acceptance",True),
                        ("source_base_head","0"*40),
                        ("source_module","Foreign.Module"),
                        ("conditional_transfer_status","PROVED"),
                        ("old_external_Deduction_G_binding","ASSUMED")):
      with self.subTest(field=field):
        altered=dict(contract); altered[field]=value
        with self.assertRaises(scope.ScopeError):
          scope.validate_semantics(altered,source)
    for old,new in (
         ("smallPrimeCenter N","(0:ℝ)"),
         ("discretePrimeMean p","(1/2:ℝ)"),
         ("smallPrimeCutoff N < (p:ℝ)","smallPrimeCutoff N ≤ (p:ℝ)"),
         ("Finset.Icc K ⌊(K:ℝ)^((3:ℝ)/2)⌋₊","Finset.Ico K ⌊(K:ℝ)^((3:ℝ)/2)⌋₊"),
         ("ArithmeticFunction.vonMangoldt n","(0:ℝ)"),
         ("Real.eulerMascheroniConstant","(0:ℝ)")):
      self.assertIn(old,source)
      with self.subTest(source_part=old):
        with self.assertRaises(scope.ScopeError):
          scope.validate_semantics(contract,source.replace(old,new))
    with self.assertRaises(scope.ScopeError):
      scope.validate_semantics(contract,source+"\naxiom fakeBridge : False\n")

  def test_adversarial_git_source_and_parent_scope(self):
    from unittest.mock import patch
    target=scope
    if (scope.REPO/"research/RHRC/integration/opica_next_epoch/SOURCE_EPOCH.json").is_file():
      from research.RHRC.integration.opica_next_epoch import scope as target
    original=target.git
    def changed_parent(*a):
      if a==("rev-parse",scope.BASE+"^{tree}"): return "0"*40
      return original(*a)
    with patch.object(target,"git",side_effect=changed_parent):
      with self.assertRaises(target.ScopeError):
        scope.assert_source()
    def extra_path(*a):
      if a==("diff","--name-status",scope.BASE,"HEAD"):
        return original(*a)+"\nA\tUNREVIEWED.txt"
      return original(*a)
    with patch.object(target,"git",side_effect=extra_path):
      with self.assertRaises(target.ScopeError):
        scope.assert_source()
    def toolchain_drift(*a):
      if a==("rev-parse","HEAD:lean-toolchain"): return "0"*40
      return original(*a)
    with patch.object(target,"git",side_effect=toolchain_drift):
      with self.assertRaises(target.ScopeError):
        scope.assert_source()
  def test_clean_additive_scope(self):
    self.assertFalse(scope.assert_source()["proof_acceptance"])
if __name__=="__main__":unittest.main()
