import Zeta23.CCM.OriginalDetectorForcingError
import Zeta23.CCM.Step123PhysicalImageIdentity
import Zeta23.CCM.OriginalDetectorPaddedFiniteH1Rate

/-!
# Actual original-detector shifted forcing error, at the real packet

The general complete mixed-Weil H1 bound is here instantiated on
the *same original padded detector* selected by Step123. We prove
support/regularity of the physical finite-minus-smooth source rather
than accepting those as caller hypotheses. The upper estimate retains
the full finite-mode factor and actual eta.

This does not establish the remaining compact-inverse local duality,
the source-only asymptotic eta bound or a closing C-Schur upper law.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- Deep separation implies disjoint original lobes at the frozen scale. -/
theorem originalDetector_lateSeparation_gt_fixedScale
    {a : ℝ} (hL : 4 < fixedOriginalSincTrialAperture a) :
    UniversalSinc.fixedScale < a := by
  unfold fixedOriginalSincTrialAperture fixedOriginalSincLobeCenter
    UniversalSinc.fixedScale at hL ⊢
  norm_num at hL ⊢
  linarith

/-- The complete genuine error is the actual normalized finite source
minus the unchanged original smooth two-lobe source. -/
def Step123NativeOutput.physicalSourceError
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : ℝ → ℂ :=
  originalDetectorPaddedFinitePhysicalUnit
    (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos -
  fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a

/-- No caller-supplied C2 or compact-support assumption: both are
proved for the exact frozen native source and actual normalized image. -/
theorem Step123NativeOutput.physicalSourceError_admissible
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ContDiff ℝ 2 out.physicalSourceError ∧
      tsupport out.physicalSourceError ⊆
        Icc (0 : ℝ) (fixedOriginalSincTrialAperture a) := by
  let L := fixedOriginalSincTrialAperture a
  let phase := nativeOriginalDetectorPhaseSign σ
  let f := originalDetectorPaddedFinitePhysicalUnit phase a out.aperture_pos
  let g := fixedOriginalSincPhaseTrial phase a
  have ha : UniversalSinc.fixedScale < a :=
    originalDetector_lateSeparation_gt_fixedScale out.aperture_gt_four
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hf : ContDiff ℝ 2 f :=
    contDiff_const.mul (originalDetectorPaddedFiniteOriginalPhaseHard_contDiff
      ha0 phase out.aperture_pos)
  have hg : ContDiff ℝ 2 g := fixedOriginalSincPhaseTrial_contDiff phase a
  have hs : tsupport (f - g) ⊆ Icc (0 : ℝ) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hout
    have hf0 : f x = 0 := by
      dsimp [f, originalDetectorPaddedFinitePhysicalUnit,
        originalDetectorPaddedFiniteOriginalPhaseHard]
      rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hout]
      simp
    have hg0 : g x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hb := fixedOriginalSincPhaseTrial_support ha phase hm
      exact hout ⟨by linarith [hb.1], by linarith [hb.2]⟩
    exact hx (by simp [Pi.sub_apply, hf0, hg0])
  exact ⟨hf.sub hg, hs⟩

/-- The actual shifted mixed forcing approximation, not an arbitrary
stand-in error or projected source.  The vector v is a true native
predecessor test on the same physical aperture and phase. -/
theorem Step123NativeOutput.actualProjectedForcing_error_bound
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ∃ C_Q : ℝ, 0 < C_Q ∧
      ∀ (v : nativePoleNeutralParitySpace σ
        (fixedOriginalSincTrialAperture a)
        (out.retained.state.selection.cutoff - 1)),
        ‖zetaZeroConfig.W out.physicalSourceError
          (finitePhysicalSynthesis
            (fixedOriginalSincTrialAperture a)
            (out.retained.state.selection.cutoff - 1)
            (canonicalNativeCoefficientInclusion σ
              (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1) v)) +
          (out.retained.state.selection.eta : ℂ) *
            EF.weilTest out.physicalSourceError
              (finitePhysicalSynthesis
                (fixedOriginalSincTrialAperture a)
                (out.retained.state.selection.cutoff - 1)
                (canonicalNativeCoefficientInclusion σ
                  (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1) v)) 0‖ ≤
          (C_Q * (1 + fixedOriginalSincTrialAperture a) *
            Real.exp (fixedOriginalSincTrialAperture a / 2) *
            Real.sqrt (1 +
              (2 * Real.pi *
                (out.retained.state.selection.cutoff - 1 : ℕ) /
                fixedOriginalSincTrialAperture a) ^ 2) +
            out.retained.state.selection.eta) *
            nativePhysicalH1Norm out.physicalSourceError * ‖v‖ := by
  obtain ⟨C_Q, hC, hQ⟩ := originalDetector_forcing_error_bound
  have hEtaPos : 0 ≤ out.retained.state.selection.eta := by
    have hExp : 0 < Real.exp (β * fixedOriginalSincTrialAperture a) := Real.exp_pos _
    have h1 : 0 < Real.exp (β * fixedOriginalSincTrialAperture a) / 3 := by positivity
    exact (h1.trans out.source_selector.eta_lower).le
  obtain ⟨hC2, hSupport⟩ := out.physicalSourceError_admissible
  exact ⟨C_Q, hC, fun v =>
    hQ σ (fixedOriginalSincTrialAperture a) out.aperture_pos
      (out.retained.state.selection.cutoff - 1)
      out.retained.state.selection.eta hEtaPos out.physicalSourceError
      hC2 hSupport v⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetector_lateSeparation_gt_fixedScale
#print axioms Zeta23.CCM.Step123NativeOutput.physicalSourceError_admissible
#print axioms Zeta23.CCM.Step123NativeOutput.actualProjectedForcing_error_bound
