import Zeta23.CCM.Step123OutputData
import Zeta23.CCM.OriginalDetectorPaddedFinitePhysicalUnitBridge
import Zeta23.CCM.NativeOriginalExteriorHistory
import Zeta23.CCM.NativeIntegerPrimeField

/-!
# Step123 typed native field consumers, source and actual selected state

Each theorem below *consumes a real constructed Step123NativeOutput* or
the literal frozen fixed-scale source. These are typed mathematical
consumers for the original 44-field contract, not a claim that all
N01-N40/G01-G04 fields, the independently reviewed receipt or D2 have
been finished.

No new source, detector, inverse, unknown zeta zero, conditional closing
law or global exterior L2 premise is introduced.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- N01-N04: literal fixed-source density, compact support,
probability mass, symmetry, real nonnegativity and paper transform. -/
theorem step123_fixed_source_evidence :
    (∀ x : ℝ, 0 ≤ universalSincSource UniversalSinc.fixedScale x) ∧
    tsupport (universalSincSource UniversalSinc.fixedScale) ⊆
      Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale ∧
    Function.Even (universalSincSource UniversalSinc.fixedScale) ∧
    (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1 ∧
    Zeta23.paperFT
      (fun x : ℝ => (universalSincSource UniversalSinc.fixedScale x : ℂ)) =
      UniversalSinc.product UniversalSinc.fixedScale := by
  exact ⟨universalSincSource_nonneg UniversalSinc.fixedScale_pos,
    universalSincSource_support UniversalSinc.fixedScale_pos,
    universalSincSource_even UniversalSinc.fixedScale_pos,
    universalSincSource_integral_one UniversalSinc.fixedScale_pos,
    paperFT_universalSincSource UniversalSinc.fixedScale_pos⟩

/-- N05-N07: the unchanged original phase and physically reflected
second lobe, without equating its phase to the later selected ground. -/
theorem Step123NativeOutput.original_trial_reflected
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (x : ℝ) :
    out.originalTrial x =
      (fixedOriginalSincTrialNormalization : ℂ) *
        (fixedOriginalSincKernel (x - fixedOriginalSincLobeCenter) +
          (nativeOriginalDetectorPhaseSign σ : ℂ) *
          fixedOriginalSincKernel
            (fixedOriginalSincTrialAperture a - x -
              fixedOriginalSincLobeCenter)) := by
  exact fixedOriginalSincPhaseTrial_reflected_formula
    (nativeOriginalDetectorPhaseSign σ) a x

/-- N11-N12/N17: the actual retained original detector has unit norm
and comes from precisely the registered padded finite source. -/
theorem Step123NativeOutput.detector_source_unit
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.retained.state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        (by linarith [out.aperture_gt_four]) ∧
      ‖out.retained.state.detector‖ = 1 :=
  ⟨out.detector_source_eq, out.retained.state.detector_unit⟩

/-- N18-N20: lambda is the actual selected ground eigenvalue
at its own parity and cutoff, not the detector shift -eta. -/
theorem Step123NativeOutput.selected_ground_eigen
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ‖out.selectedGround‖ = 1 ∧
    nativePoleNeutralParityCanonical out.retained.state.selectedParity
      (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.cutoff out.selectedGround =
      (out.retained.state.selection.lam : ℂ) • out.selectedGround := by
  exact ⟨out.retained.state.selectedGround_unit,
    out.retained.state.selectedGround_eigen⟩

/-- N13: the genuine finite L2 image is the native original unit
detector, not the separate smooth two-lobe trial. -/
theorem Step123NativeOutput.finite_image_unit
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ‖out.physicalFiniteImage‖ = 1 :=
  out.physicalFiniteImage_unit

/-- N14: the spectral finite-mode factor appears in the actual
physical H1 estimate at Kd=ceil(L^4). This is not an unsupported
uniform bound on eta. -/
theorem Step123NativeOutput.finite_image_H1_bound
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    originalDetectorPhysicalH1Error
      (finitePhysicalSynthesis
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        (canonicalNativeCoefficientInclusion σ
          (fixedOriginalSincTrialAperture a)
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
          out.retained.state.detector)) 0 ≤
      Real.sqrt (1 +
        (2 * Real.pi *
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
          fixedOriginalSincTrialAperture a) ^ 2) := by
  have h := canonicalNativePhysicalSynthesis_H1_bound σ
    out.aperture_pos
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    out.retained.state.detector
  rw [out.retained.state.detector_unit, mul_one] at h
  exact h

/-- N29-N30: the arithmetic view contains the exact fixed native
prime field and integer drive, not reconstructed trial or ground data. -/
theorem Step123NativeOutput.arithmeticView_eq_fixed
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.arithmeticData.1 = nativeOriginalPrimeField ∧
    out.arithmeticData.2 = nativeOriginalIntegerDrive := ⟨rfl, rfl⟩

/-- N31: actual causal-completion quantities are the native input and
correction, with no global inverse or A-X/B-Y assumption. -/
theorem Step123NativeOutput.rangeView_eq_actual
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.rangeData.1 = nativeCompletedInput ∧
    out.rangeData.2 = nativeCompletionCorrection := ⟨rfl, rfl⟩

/-- N35/N38: exact *one* original selected forcing vector. A changed
detector or selected ground cannot satisfy this by a rename. -/
theorem Step123NativeOutput.original_forcing_source_bound
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.retained.predecessorForcing =
      originalDetectorNativeForcing σ out.retained.state.selection
        out.retained.state.detector :=
  out.retained.forcing_eq

/-- N39: the original smooth physical response decomposes as its
separate left exterior, potentially nonzero interior and right exterior. -/
theorem Step123NativeOutput.original_response_reconstruction
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (x : ℝ) :
    out.smoothOriginal.response x =
      out.smoothOriginal.left x +
      out.smoothOriginal.interior x +
      out.smoothOriginal.right x :=
  out.smoothOriginal.reconstruction x

/-- N36/N40: every original prime translation remains in the exact
smooth source history, including the reflected terms and sign. -/
theorem Step123NativeOutput.original_prime_histories
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (x : ℝ) :
    nativeWeilPrimeResponse (out.originalTrial) x =
      out.smoothOriginal.primeHistories x :=
  out.smoothOriginal.prime_eq x

/-- N25: correct full detector-complement loss, not the selected
ground one-shell scalar. -/
theorem Step123NativeOutput.originalSchur_full_complement
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    let state := out.retained.state
    let y := isometricDetectorComplementCoordinate
      (nativeDetectorPredecessorEmbedding σ state.selection)
      state.detector
    y ≠ 0 ∧
      (inner ℂ (nativeDetectorSchurOperator σ state.inverses y) y).re <
        -(Real.exp (β * fixedOriginalSincTrialAperture a)) / 2 :=
  out.originalDetector_schur_loss

end Zeta23.CCM

#print axioms Zeta23.CCM.step123_fixed_source_evidence
#print axioms Zeta23.CCM.Step123NativeOutput.finite_image_H1_bound
#print axioms Zeta23.CCM.Step123NativeOutput.original_forcing_source_bound
#print axioms Zeta23.CCM.Step123NativeOutput.original_prime_histories
#print axioms Zeta23.CCM.Step123NativeOutput.originalSchur_full_complement
