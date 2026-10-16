import Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageTransport

/-! All required fourth-order hard-extension seams of the padded actual `Pq`. -/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

theorem originalDetectorPaddedFinitePoleImage_endpoint_jets_lt_six
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) {r : ℕ} (hr : r < 6) :
    iteratedDeriv r (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith))) 0 = 0 ∧
    iteratedDeriv r (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith))) L = 0 := by
  have hLp : 0 < L := by linarith
  have hf : ContDiff ℝ (⊤ : ℕ∞) (originalDetectorPaddedFiniteWindowImage s L c hLp) :=
    (originalDetectorPaddedFiniteWindow_contDiff L).mul
      (originalDetectorPaddedRawFourierPartialSum_contDiff s L c hLp)
  have hhi := originalDetectorPaddedFiniteWindowImage_endpoint_jets_lt_eight s c hLp
    (by omega : r + 2 < 8)
  have hlo := originalDetectorPaddedFiniteWindowImage_endpoint_jets_lt_eight s c hLp
    (by omega : r < 8)
  simp only [localizedFiniteFunction_originalDetectorPaddedFinitePoleImageCoefficients s c hL,
    padded_iteratedDeriv_poleKilled_infty hf, hhi.1, hhi.2, hlo.1, hlo.2, mul_zero, sub_self,
    and_self]

theorem originalDetectorPaddedFinitePoleImage_hard_contDiff_four
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ContDiff ℝ 4 (localizedFiniteVector L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith))) := by
  have hLp : 0 < L := by linarith
  rw [localizedFiniteVector_eq_indicator]
  apply padded_contDiff_nat_indicator_Icc_of_iteratedDeriv_endpoint_zero hLp 4
  · unfold localizedFiniteFunction
    apply ContDiff.sum
    intro i hi
    exact contDiff_const.mul ((contDiff_localizedMode L _).of_le le_top)
  · intro r hr
    exact originalDetectorPaddedFinitePoleImage_endpoint_jets_lt_six s c hL (by omega)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImage_endpoint_jets_lt_six
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImage_hard_contDiff_four
