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
  def test_clean_additive_scope(self):
    self.assertFalse(scope.assert_source()["proof_acceptance"])
if __name__=="__main__":unittest.main()
