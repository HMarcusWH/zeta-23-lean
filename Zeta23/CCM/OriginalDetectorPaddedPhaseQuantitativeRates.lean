import Zeta23.CCM.OriginalDetectorPaddedFourierQuantitativeRates
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseWeilPadding

/-! Quantitative retained margins for actual phase mass and Weil errors. -/

noncomputable section

open Filter
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

theorem originalDetectorPaddedMassBudget_mul_quarticWeight_tendsto_zero (σ β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseMassErrorBudget σ L *
      originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β) atTop (𝓝 0) := by
  let C := fixedOriginalSincTrialNormalization * (1 + |σ|)
  let M := C * padded_originalDetectorKernelSupBudget UniversalSinc.fixedScale
  have hlinear := (originalDetectorPaddedPoleBudget_mul_aperture_quarticWeight_tendsto_zero
    UniversalSinc.fixedScale 0 β).const_mul C
  have hzero := originalDetectorPaddedFinitePoleImageJetBudget_mul_exp_tendsto_zero UniversalSinc.fixedScale 0 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hzero
  have hfactor : Tendsto (fun L : ℝ =>
      2 * M + C * originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L 0)
      atTop (𝓝 (2 * M + C * 0)) := tendsto_const_nhds.add (hzero.const_mul C)
  have hprod := hlinear.mul hfactor
  simp only [mul_zero, add_zero, zero_mul] at hprod
  convert! hprod using 1
  ext L
  unfold originalDetectorPaddedFinitePhaseMassErrorBudget
  dsimp [C, M]
  ring

theorem originalDetectorPaddedL1Budget_mul_quarticWeight_tendsto_zero (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseL1ErrorBudget L r *
      originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β) atTop (𝓝 0) := by
  have hh := (originalDetectorPaddedPoleBudget_mul_aperture_quarticWeight_tendsto_zero
    UniversalSinc.fixedScale r β).const_mul (2 * fixedOriginalSincTrialNormalization)
  simpa only [mul_zero, originalDetectorPaddedFinitePhaseL1ErrorBudget, mul_assoc] using hh

theorem originalDetectorPaddedWeilBudget_mul_quarticWeight_tendsto_zero (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseWeilErrorBudget L *
      originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β) atTop (𝓝 0) := by
  let H0 := originalDetectorOriginalPhaseL1JetBudget 0
  let H2 := originalDetectorOriginalPhaseL1JetBudget 2
  have hE0 := originalDetectorPaddedL1Budget_mul_quarticWeight_tendsto_zero 0 (β + 1)
  have hE2 := originalDetectorPaddedL1Budget_mul_quarticWeight_tendsto_zero 2 (β + 1)
  have hzero := originalDetectorPaddedFinitePhaseL1ErrorBudget_mul_exp_tendsto_zero 0 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hzero
  have hsum : Tendsto (fun L : ℝ =>
      (originalDetectorPaddedFinitePhaseL1ErrorBudget L 0 + originalDetectorPaddedFinitePhaseL1ErrorBudget L 2) *
        originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L (β + 1)) atTop (𝓝 0) := by
    simpa only [add_zero, ← add_mul] using hE0.add hE2
  have hbounded : Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseL1ErrorBudget L 0 + H0)
      atTop (𝓝 H0) := by simpa only [zero_add] using hzero.add_const H0
  have hlim := ((hsum.mul hbounded).add (hE0.const_mul (H0 + H2))).const_mul zetaInvSqZeroMass
  simp only [mul_zero, zero_mul, add_zero] at hlim
  convert! hlim using 1
  ext L
  unfold originalDetectorPaddedFinitePhaseWeilErrorBudget
  dsimp [H0, H2]
  have he : originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L (β + 1) =
      Real.exp L * originalDetectorQuarticErrorWeight UniversalSinc.fixedScale L β := by
    unfold originalDetectorQuarticErrorWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- General extraction of a retained source-only stretched-exponential
margin. The constants and cutoff schedule are theorem-defined upstream. -/
theorem eventually_lt_retained_quartic_envelope
    (s : ℝ) {B : ℝ → ℝ}
    (hB : Tendsto (fun L => B L * originalDetectorQuarticErrorWeight s L 0) atTop (𝓝 0)) :
    ∀ᶠ L : ℝ in atTop, B L <
      Real.exp (-originalDetectorRetainedDecayRate s * originalDetectorQuarticRootScale L) := by
  filter_upwards [hB.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with L hL
  have hm := mul_lt_mul_of_pos_right hL
    (Real.exp_pos (-originalDetectorRetainedDecayRate s * originalDetectorQuarticRootScale L))
  have he : originalDetectorQuarticErrorWeight s L 0 *
      Real.exp (-originalDetectorRetainedDecayRate s * originalDetectorQuarticRootScale L) = 1 := by
    unfold originalDetectorQuarticErrorWeight
    rw [← Real.exp_add]
    have hz : originalDetectorRetainedDecayRate s * originalDetectorQuarticRootScale L + 0 * L +
        -originalDetectorRetainedDecayRate s * originalDetectorQuarticRootScale L = 0 := by ring
    rw [hz, Real.exp_zero]
  simpa only [mul_assoc, he, mul_one, one_mul] using hm

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedMassBudget_mul_quarticWeight_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorPaddedWeilBudget_mul_quarticWeight_tendsto_zero
#print axioms Zeta23.CCM.eventually_lt_retained_quartic_envelope
