"""Actual source consumers and matched native semantic rejections.

Typed rejection concerns the attempted inference. It does not establish the
mathematical negation of an unproved source theorem.
"""
import functools,json,unittest
from pathlib import Path
from research.RHRC.integration.opica_composition.contracts import SearchBudget
from research.RHRC.integration.opica_composition.executor import run_worker
from research.RHRC.integration.opica_composition.tests.test_executor import native_context,fresh,calibration
from research.RHRC.integration.opica_round3.validate_contract import semantic_control_pair,require_semantic_rejection

HEADER="""import Zeta23.OPICARound3.Validation.NewbornSource
noncomputable section
open Zeta23.OPICARound3 Zeta23.OPICARound3.Validation Zeta23.CCM
set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace
"""

@functools.lru_cache(None)
def native_pair(positive,negative,label):
    worker,_,_=native_context(); results=[]
    for mode,source in (("positive",positive),("negative",negative)):
        out=fresh(label+"-"+mode); out.mkdir()
        (out/"Consumer.lean").write_text(source,encoding="utf-8")
        record=run_worker(worker,out,"Consumer.lean","Consumer.olean",SearchBudget(**(worker.budget or {})))
        if record["resource_status"]: raise AssertionError("RESOURCE_EXHAUSTED "+str(out))
        code=record["exit_code"]
        if mode=="positive":
            if code!=0: raise AssertionError("genuine native positive control failed: "+str(out))
        else:
            if code!=1: raise AssertionError("native negative must reject ordinarily, no crash: "+str(out))
            require_semantic_rejection((out/"Consumer.lean.log").read_text(encoding="utf-8"))
        results.append(record)
    return results

def frozen_pair(index):
    positive,negative,label=semantic_control_pair(index)
    return native_pair(positive,negative,label)

class NativeEvidenceCases(unittest.TestCase):
    def test_t21(self): frozen_pair(1)
    def test_t22(self): frozen_pair(2)
    def test_t23(self): frozen_pair(3)
    def test_t25(self): frozen_pair(4)

    def test_t24(self):
        # Exact finite scalar-operator countermodel to the general inference.
        # This does not claim distinct eigenvalues at an actual canonical cutoff.
        positive="""import Mathlib
example : (3 : ℕ) = 3 ∧ (-1 : ℚ) < 0 ∧ (-2 : ℚ) < 0 ∧ (-1 : ℚ) ≠ -2 := by norm_num
example (a b : ℚ) (h : a = b) : a = b := h
"""
        negative=positive.replace("(h : a = b) : a = b := h","(h : (3 : ℕ) = 3) : a = b := h")
        native_pair(positive,negative,"equal_cutoff_not_equal_scalar_eigenvalue")

    def test_t26(self):
        positive=HEADER+"""example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (w : nativePoleNeutralParitySpace .odd L K) (lam : ℝ) :
    nativePoleNeutralParityShifted .even L K lam (nativeParityTransfer .odd hL K w) =
      nativeParitySourceOutput .odd hL K w lam := by
  exact nativeParitySource_shifted_equation .odd hL K hK w lam
"""
        negative=positive.replace("=\n      nativeParitySourceOutput","=\n      -nativeParitySourceOutput")
        native_pair(positive,negative,"odd_source_sign")

    def test_t27(self):
        positive,_,_=semantic_control_pair(4)
        negative=positive.replace("(Ko ≤ Ke → Nonempty (NativeNewbornSourceWitness .even L (max Ke Ko) hL))",
                                  "Nonempty (NativeNewbornSourceWitness .even L (max Ke Ko) hL)")
        self.assertNotEqual(positive,negative)
        native_pair(positive,negative,"earlier_sector_not_newborn")

    def test_t28(self):
        positive=HEADER+"""example {L : ℝ} (hL : 0 < L) (p : ReversalParity) (K : ℕ)
    (W : NativeNewbornSourceWitness p L K hL) : NativeSchurWitnessRealization p L K W.e W.w := W.realization
"""
        # Dropping the resonant disjunct changes the actual dependent realization.
        negative=HEADER+"""example {L : ℝ} (hL : 0 < L) (p : ReversalParity) (K : ℕ)
    (W : NativeNewbornSourceWitness p L K hL) :
    let J := newbornCutoffInclusion p L K
    let T := nativePoleNeutralParityCanonical p L K
    ∃ hb : J.toLinearMap.adjoint (T W.e.val) ∈ (predecessorBlock J T).range,
      oneShellSchurScalar J T W.e hb < 0 ∧ W.w = regularSchurWitness J T W.e hb ∧
      (inner ℂ (T W.w) W.w).re = oneShellSchurScalar J T W.e hb := W.realization
"""
        native_pair(positive,negative,"resonant_branch_cannot_disappear")

    def test_t29(self):
        positive=HEADER+"""example {L : ℝ} (hL : 0 < L) (p : ReversalParity) : PoleNeutralParityPSD p L 2 :=
  poleNeutralParityPSD_two hL p
"""
        negative=positive.replace("PoleNeutralParityPSD p L 2","PoleNeutralParityNegative p L 2")
        native_pair(positive,negative,"empty_K2_no_negative_vector")

    def test_t30(self):
        # Preserve all 17 authored classifications. Their authority remains
        # authored review plus separately replayed native/countermodel evidence.
        native_context()
        root=Path(__file__).resolve().parents[2]/"opica_round3/atlas/SEMANTIC_OVERLAY.json"
        rows=json.loads(root.read_text(encoding="utf-8"))["connections"]
        self.assertEqual(len(rows),17)
        self.assertGreater(len({str(row.get("disposition",row.get("classification",row.get("status")))) for row in rows}),1)
        frozen_pair(4)

    def test_t78(self):
        calibration("D05"); calibration("D04")
        positive=HEADER+"""example {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K)
    (hboth : BothNeutralNegative L K) :
    ∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧ EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko := by
  obtain ⟨Ke, Ko, hKe, hKo, he, ho, _⟩ := first_simultaneous_neutral_negative_cutoff hL hK hboth
  exact ⟨Ke, Ko, hKe, hKo, he, ho⟩
"""
        negative=HEADER+"""example {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 3 ≤ K)
    (hboth : BothNeutralNegative L K) : BothNeutralNegative L K := by
  exact first_simultaneous_neutral_negative_cutoff hL hK hboth
"""
        native_pair(positive,negative,"D04_packet_not_D05_input")

    def test_t79(self):
        calibration("D05")
        positive="""import Mathlib
example (P : ℕ → Prop) (a b : ℕ) (h : a = b) (ha : P a) : P b := h ▸ ha
"""
        negative=positive.replace("(h : a = b) ","").replace("h ▸ ha","ha")
        native_pair(positive,negative,"dependent_cutoff_needs_equality_transport")

    def test_t113(self):
        calibration("D05")
        positive=HEADER+"""example {L : ℝ} (hL : 0 < L) (p : ReversalParity) (K : ℕ)
    (W : NativeNewbornSourceWitness p L K hL) : NativeSchurWitnessRealization p L K W.e W.w := W.realization
"""
        negative=positive.replace("W.e W.w := W.realization","W.e ((2 : ℂ) • W.w) := W.realization")
        native_pair(positive,negative,"scaled_w_not_original_realization")
