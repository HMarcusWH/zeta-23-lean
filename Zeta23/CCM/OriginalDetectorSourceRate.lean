import Zeta23.CCM.OriginalDetectorActualForcingError
import Zeta23.CCM.OriginalDetectorPaddedFiniteH1Rate

/-!
# Actual source-only H1 rate at the generated original detector

The constants are constructed from the fixed q_s0/k_s0 source, not
fitted to a hypothetical zero.  This is a norm-error theorem for
the literal padded finite-minus-smooth trial; it neither proves
the C-Schur upper law nor assumes the original prime field belongs
globally to L2. The selected ground never substitutes for this source.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

private theorem originalDetector_physicalH1Error_sub_zero
    (f g : ℝ → ℂ) :
    nativePhysicalH1Norm (f - g) =
      originalDetectorPhysicalH1Error f g := by
  unfold nativePhysicalH1Norm originalDetectorPhysicalH1Error
  simp only [sub_zero, Pi.sub_apply, Pi.zero_apply]

/-- Source-only constants and a source-only threshold control the full
physical H1 error of every sufficiently late generated source phase. -/
theorem step123_originalSource_H1_concrete_rate :
    ∃ C c L0 : ℝ, 0 < C ∧ 0 < c ∧ 4 ≤ L0 ∧
      ∀ {β : ℝ} {σ : ReversalParity} {a : ℝ}
        (out : Step123NativeOutput β σ a),
        L0 ≤ fixedOriginalSincTrialAperture a →
          nativePhysicalH1Norm out.physicalSourceError ≤
            C * (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (-c *
                originalDetectorQuarticRootScale
                  (fixedOriginalSincTrialAperture a)) := by
  obtain ⟨C, c, L0, hC, hc, hL0, hRate⟩ :=
    originalDetectorPaddedFinitePhysicalUnit_H1_concrete_rate
  refine ⟨C, c, L0, hC, hc, hL0, ?_⟩
  intro β σ a out hlarge
  have hσ : nativeOriginalDetectorPhaseSign σ = 1 ∨
      nativeOriginalDetectorPhaseSign σ = -1 := by
    cases σ <;> simp [nativeOriginalDetectorPhaseSign]
  have ha : UniversalSinc.fixedScale < a :=
    originalDetector_lateSeparation_gt_fixedScale out.aperture_gt_four
  have h := hRate (nativeOriginalDetectorPhaseSign σ) a
    hσ ha out.aperture_pos hlarge
  change nativePhysicalH1Norm
      (originalDetectorPaddedFinitePhysicalUnit
        (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos -
        fixedOriginalSincPhaseTrial
          (nativeOriginalDetectorPhaseSign σ) a) ≤ _ 
  rw [originalDetector_physicalH1Error_sub_zero]
  exact h

end Zeta23.CCM

#print axioms Zeta23.CCM.step123_originalSource_H1_concrete_rate
