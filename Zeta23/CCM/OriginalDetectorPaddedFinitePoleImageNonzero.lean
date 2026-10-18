import Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageAsymptotics
import Zeta23.ExceptionalZero.UniversalSincOriginalPhaseDepth

/-! # Cofinal nonvanishing and literal normalization of the actual finite image -/

noncomputable section

open Set Complex Filter MeasureTheory
open scoped Topology

namespace Zeta23.CCM

/-- The actual fixed source produces nonzero finite vectors at every
sufficiently large aperture, uniformly over all centers with the proved
unit collars. No nonvanishing hypothesis is supplied by the caller. -/
theorem exists_originalDetectorPaddedFinitePoleImageCoefficients_nonzero_threshold :
    ∃ (L0 : ℝ) (hL0 : 2 ≤ L0), ∀ (L : ℝ) (hL : L0 ≤ L) (c : ℝ),
      1 + UniversalSinc.fixedScale ≤ c → c + UniversalSinc.fixedScale ≤ L - 1 →
      originalDetectorPaddedFinitePoleImageCoefficients UniversalSinc.fixedScale L c
        (by linarith [hL0]) ≠ 0 := by
  have hne : ∃ x : ℝ, Zeta23.ExceptionalZero.fixedOriginalSincKernel x ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hfun : Zeta23.ExceptionalZero.fixedOriginalSincKernel = fun _ => (0 : ℂ) := funext hnone
    have hmass := Zeta23.ExceptionalZero.fixedOriginalSincKernel_integral
    rw [hfun, integral_zero] at hmass
    norm_num at hmass
  obtain ⟨x0, hx0⟩ := hne
  have hxmem : x0 ∈ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale := by
    by_contra hout
    exact hx0 (universalSincKernel_zero_outside UniversalSinc.fixedScale_pos hout)
  have hnorm : 0 < ‖Zeta23.ExceptionalZero.fixedOriginalSincKernel x0‖ := norm_pos_iff.mpr hx0
  have hlim := originalDetectorPaddedFinitePoleImageJetBudget_mul_exp_tendsto_zero
    UniversalSinc.fixedScale 0 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hlim
  have hevent := hlim.eventually (gt_mem_nhds hnorm)
  obtain ⟨B, hB⟩ := (eventually_atTop.1 hevent)
  refine ⟨max 2 B, le_max_left _ _, ?_⟩
  intro L hL c hleft hright hzero
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hsmall := hB L ((le_max_right _ _).trans hL)
  have hx : x0 + c ∈ Icc (0 : ℝ) L := by
    constructor <;> linarith [hxmem.1, hxmem.2]
  have herr := originalDetectorPaddedFinitePoleImage_iteratedDeriv_error_le_budget
    UniversalSinc.fixedScale_pos hL2 hleft hright 0 hx
  simp only [iteratedDeriv_zero, add_sub_cancel_right] at herr
  have hvalue : localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePoleImageCoefficients UniversalSinc.fixedScale L c (by linarith))
        (x0 + c) = 0 := by
    rw [hzero]
    simp [localizedFiniteFunction]
  rw [hvalue, sub_zero] at herr
  exact (not_le_of_gt hsmall) herr

/-- Literal normalization in the existing coefficient Euclidean metric. -/
def originalDetectorPaddedFinitePoleImageNormalized (s L c : ℝ) (hL : 0 < L) :
    EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1)) :=
  ((‖WithLp.toLp 2 (originalDetectorPaddedFinitePoleImageCoefficients s L c hL)‖⁻¹ : ℝ) : ℂ) •
    WithLp.toLp 2 (originalDetectorPaddedFinitePoleImageCoefficients s L c hL)

/-- Normalization has exactly unit norm whenever the actual finite vector
is nonzero; the preceding theorem constructs the fixed-source threshold. -/
theorem norm_originalDetectorPaddedFinitePoleImageNormalized
    (s L c : ℝ) (hL : 0 < L)
    (hne : originalDetectorPaddedFinitePoleImageCoefficients s L c hL ≠ 0) :
    ‖originalDetectorPaddedFinitePoleImageNormalized s L c hL‖ = 1 := by
  have hv : WithLp.toLp 2 (originalDetectorPaddedFinitePoleImageCoefficients s L c hL) ≠ 0 := by
    intro hz
    apply hne
    exact (WithLp.toLp_injective 2) hz
  unfold originalDetectorPaddedFinitePoleImageNormalized
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_originalDetectorPaddedFinitePoleImageCoefficients_nonzero_threshold
#print axioms Zeta23.CCM.norm_originalDetectorPaddedFinitePoleImageNormalized
