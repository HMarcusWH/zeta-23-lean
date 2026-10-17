import Zeta23.CCM.OriginalDetectorPaddedFiniteNativeFormConcreteRate
import Zeta23.CCM.Step123PhysicalImageIdentity
import Zeta23.CCM.OriginalDetectorActualForcingError
import Zeta23.ExceptionalZero.Step123OutputProducer

/-!
# N14: same-state image errors of the stored Step 1-3 detector

Field N14 (`image.errors`) asks for the actual physical H1 error and the
requested concrete native-form error of the ONE stored detector, with one
common threshold that depends only on the frozen source.

What is proved here:

* `Step123NativeOutput.detectorCoefficients_eq_paddedUnit`,
  `Step123NativeOutput.detectorNativeEnergy_eq_paddedNativeEnergy`,
  `Step123NativeOutput.physicalSourceError_eq_storedDetector` and
  `Step123NativeOutput.physicalFiniteImage_ae_eq_paddedUnit` identify the
  packet's own stored detector (`out.retained.state.detector`), its native
  self-energy, its physical L2 image and `out.physicalSourceError` with the
  literal true-normalized padded source objects. They use only the packet
  fields `detector_source_eq` and the existing N13 identity.
* `step123NativeOutput_imageErrors_at_sourceThreshold`: every stored
  packet `out : Step123NativeOutput β σ a` already pays the named source-only
  `originalDetectorPaddedImageThreshold`, so no extra aperture hypothesis is
  needed. For that stored packet,
  the physical H1 error of the stored detector's physical synthesis against
  the original smooth phase trial `out.originalTrial`, the H1 norm of
  `out.physicalSourceError`, and the native-form error
  `|Re q(stored detector) - Re W(originalTrial, originalTrial)|` obey the
  concrete rates of `originalDetectorPaddedFinitePhysicalUnit_common_error_rates`
  (constant one and decay rate `originalDetectorRetainedDecayRate fixedScale`).
  `step123NativeOutput_imageErrors_commonThreshold` retains the quantified
  compatibility form, explicitly witnessed by that same named threshold.
* `exists_generatedStep123Output_imageErrors_cofinal` and
  `exists_generatedStep123Output_imageErrors_cofinal_atLateness`: the
  existing generated producer, called at lateness `max R L0`, yields for each
  actual off-line zero, horizontal exponent, phase and lateness `R` a
  generated packet whose aperture exceeds `max R L0`, so the same-state rates
  above apply to its stored native packet. The second form only weakens the
  produced lateness certificate from `max R L0` to `R`; every other field is
  copied unchanged from the producer output.

What is NOT proved here: no Step 4 law, no C-Schur upper estimate, no
A-X/B-Y closure, no completion of the full 44-field producer, no D2 gate, and
no Riemann hypothesis. The two phases are not given a common aperture.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- The H1 norm of a difference is the H1 error of the pair (this repeats a
private two-line unfolding in `OriginalDetectorSourceRate`). -/
private theorem nativePhysicalH1Norm_sub_eq_physicalH1Error (f g : ℝ → ℂ) :
    nativePhysicalH1Norm (f - g) = originalDetectorPhysicalH1Error f g := by
  unfold nativePhysicalH1Norm originalDetectorPhysicalH1Error
  simp only [sub_zero, Pi.sub_apply, Pi.zero_apply]

/-- The Euclidean coefficients of the packet's stored detector are the
literal true-normalized padded phase unit vector. -/
theorem Step123NativeOutput.detectorCoefficients_eq_paddedUnit
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    canonicalNativeCoefficientInclusion σ
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector =
      originalDetectorPaddedFinitePhaseUnitVector
        (nativeOriginalDetectorPhaseSign σ) (fixedOriginalSincTrialAperture a)
        fixedOriginalSincLobeCenter out.aperture_pos := by
  rw [out.detector_source_eq]
  exact originalDetectorPaddedNativeUnit_eq_unitCoefficients σ _ _

/-- The native self-energy of the stored detector, computed with the
packet's own native parity operator, is the padded native energy that the
concrete native-form rate controls. -/
theorem Step123NativeOutput.detectorNativeEnergy_eq_paddedNativeEnergy
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    (inner ℂ (nativePoleNeutralParityCanonical σ
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector) out.retained.state.detector).re =
      originalDetectorPaddedNativeEnergy
        (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos := by
  rw [← nativePoleNeutralParityAmbient_energy]
  have hamb : nativePoleNeutralParityAmbient σ
      (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      out.retained.state.detector =
      canonicalNativeCoefficientInclusion σ
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector := by
    cases σ <;> rfl
  rw [hamb, out.detectorCoefficients_eq_paddedUnit]
  rfl

/-- `out.physicalSourceError` is literally the physical synthesis of the
stored detector minus the original smooth phase trial of the same packet. -/
theorem Step123NativeOutput.physicalSourceError_eq_storedDetector
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.physicalSourceError =
      finitePhysicalSynthesis
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        (canonicalNativeCoefficientInclusion σ
          (fixedOriginalSincTrialAperture a)
          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
          out.retained.state.detector) -
        out.originalTrial := by
  rw [out.finitePhysicalSource_eq_originalPadded]
  rfl

/-- The stored physical L2 image `out.physicalFiniteImage` is almost
everywhere the true-normalized padded physical function. -/
theorem Step123NativeOutput.physicalFiniteImage_ae_eq_paddedUnit
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    (out.physicalFiniteImage : ℝ → ℂ) =ᵐ[volume]
      originalDetectorPaddedFinitePhysicalUnit
        (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos := by
  rw [← out.finitePhysicalSource_eq_originalPadded]
  exact canonicalNativePhysicalIsometry_ae σ out.aperture_pos _ _

/-- N14. The named source-only threshold, paid by every native packet, makes
both actual errors of the STORED detector obey their concrete rates: the
physical H1 error against the original smooth phase trial (also stated for
`out.physicalSourceError`) and the native-form error of the stored
detector's own native self-energy against the original Weil energy. No
bridge identity, error bound, branch consequence or extra aperture bound is
a hypothesis. -/
theorem step123NativeOutput_imageErrors_at_sourceThreshold
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
          originalDetectorPhysicalH1Error
              (finitePhysicalSynthesis
                (fixedOriginalSincTrialAperture a)
                (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                (canonicalNativeCoefficientInclusion σ
                  (fixedOriginalSincTrialAperture a)
                  (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                  out.retained.state.detector))
              out.originalTrial ≤
            (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) ∧
          nativePhysicalH1Norm out.physicalSourceError ≤
            (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) ∧
          |(inner ℂ (nativePoleNeutralParityCanonical σ
                (fixedOriginalSincTrialAperture a)
                (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                out.retained.state.detector) out.retained.state.detector).re -
              (zetaZeroConfig.W out.originalTrial out.originalTrial).re| ≤
            (1 + fixedOriginalSincTrialAperture a) *
              (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (fixedOriginalSincTrialAperture a / 2 -
                originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                  originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) := by
  have hRates :=
    (Classical.choose_spec originalDetectorPaddedFinitePhysicalUnit_common_error_rates).2
  have hlarge : originalDetectorPaddedImageThreshold ≤ fixedOriginalSincTrialAperture a :=
    out.image_threshold_paid.le
  have hσ : nativeOriginalDetectorPhaseSign σ = 1 ∨
      nativeOriginalDetectorPhaseSign σ = -1 := by
    cases σ <;> simp [nativeOriginalDetectorPhaseSign]
  have ha : UniversalSinc.fixedScale < a :=
    originalDetector_lateSeparation_gt_fixedScale out.aperture_gt_four
  obtain ⟨hH1, hForm⟩ := hRates (nativeOriginalDetectorPhaseSign σ) a hσ ha
    out.aperture_pos hlarge
  refine ⟨?_, ?_, ?_⟩
  · rw [out.finitePhysicalSource_eq_originalPadded]
    exact hH1
  · rw [out.physicalSourceError_eq_storedDetector,
      nativePhysicalH1Norm_sub_eq_physicalH1Error,
      out.finitePhysicalSource_eq_originalPadded]
    exact hH1
  · rw [out.detectorNativeEnergy_eq_paddedNativeEnergy]
    exact hForm

/-- Compatibility formulation of N14, explicitly witnessed by the named
source-only threshold already paid by every native packet. -/
theorem step123NativeOutput_imageErrors_commonThreshold :
    ∃ L0 : ℝ, 4 ≤ L0 ∧
      ∀ {β : ℝ} {σ : ReversalParity} {a : ℝ}
        (out : Step123NativeOutput β σ a),
        L0 ≤ fixedOriginalSincTrialAperture a →
          originalDetectorPhysicalH1Error
              (finitePhysicalSynthesis
                (fixedOriginalSincTrialAperture a)
                (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                (canonicalNativeCoefficientInclusion σ
                  (fixedOriginalSincTrialAperture a)
                  (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                  out.retained.state.detector))
              out.originalTrial ≤
            (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) ∧
          nativePhysicalH1Norm out.physicalSourceError ≤
            (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) ∧
          |(inner ℂ (nativePoleNeutralParityCanonical σ
                (fixedOriginalSincTrialAperture a)
                (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                out.retained.state.detector) out.retained.state.detector).re -
              (zetaZeroConfig.W out.originalTrial out.originalTrial).re| ≤
            (1 + fixedOriginalSincTrialAperture a) *
              (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (fixedOriginalSincTrialAperture a / 2 -
                originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                  originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) := by
  refine ⟨originalDetectorPaddedImageThreshold,
    four_le_originalDetectorPaddedImageThreshold, ?_⟩
  intro β σ a out _hlarge
  exact step123NativeOutput_imageErrors_at_sourceThreshold out

end Zeta23.CCM

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-- N14, generated and cofinal. The threshold `L0` of
`step123NativeOutput_imageErrors_commonThreshold` is fixed before the zero.
For each actual off-line zero, admissible `β`, phase and lateness `R`, the
existing producer called at lateness `max R L0` gives a generated packet
whose aperture exceeds `max R L0`, so both same-state rates hold for its
stored native packet. Each phase is cofinal separately. -/
theorem exists_generatedStep123Output_imageErrors_cofinal :
    ∃ L0 : ℝ, 4 ≤ L0 ∧
      ∀ (ρ : zetaZeroConfig.carrier) {β : ℝ}
        (_hβ : 0 < β) (_hβρ : β < |(ρ : ℂ).re - 1 / 2|)
        (σ : ReversalParity) (R : ℝ),
        ∃ g : GeneratedStep123Output ρ β σ (max R L0),
          max R L0 < fixedOriginalSincTrialAperture g.sourceData.separation ∧
          originalDetectorPhysicalH1Error
              (finitePhysicalSynthesis
                (fixedOriginalSincTrialAperture g.sourceData.separation)
                (originalDetectorQuarticCutoff
                  (fixedOriginalSincTrialAperture g.sourceData.separation))
                (canonicalNativeCoefficientInclusion σ
                  (fixedOriginalSincTrialAperture g.sourceData.separation)
                  (originalDetectorQuarticCutoff
                    (fixedOriginalSincTrialAperture g.sourceData.separation))
                  g.native.retained.state.detector))
              g.native.originalTrial ≤
            (fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale
                  (fixedOriginalSincTrialAperture g.sourceData.separation)) ∧
          nativePhysicalH1Norm g.native.physicalSourceError ≤
            (fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale
                  (fixedOriginalSincTrialAperture g.sourceData.separation)) ∧
          |(inner ℂ (nativePoleNeutralParityCanonical σ
                (fixedOriginalSincTrialAperture g.sourceData.separation)
                (originalDetectorQuarticCutoff
                  (fixedOriginalSincTrialAperture g.sourceData.separation))
                g.native.retained.state.detector) g.native.retained.state.detector).re -
              (zetaZeroConfig.W g.native.originalTrial g.native.originalTrial).re| ≤
            (1 + fixedOriginalSincTrialAperture g.sourceData.separation) *
              (fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
              Real.exp (fixedOriginalSincTrialAperture g.sourceData.separation / 2 -
                originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                  originalDetectorQuarticRootScale
                    (fixedOriginalSincTrialAperture g.sourceData.separation)) := by
  obtain ⟨L0, hL0, hRates⟩ := step123NativeOutput_imageErrors_commonThreshold
  refine ⟨L0, hL0, ?_⟩
  intro ρ β hβ hβρ σ R
  obtain ⟨g⟩ := exists_generatedStep123Output ρ hβ hβρ σ (max R L0)
  have hlate : max R L0 < fixedOriginalSincTrialAperture g.sourceData.separation :=
    (le_max_left _ 4).trans_lt g.native_aperture_bound
  have hL : L0 ≤ fixedOriginalSincTrialAperture g.sourceData.separation :=
    ((le_max_right R L0).trans_lt hlate).le
  exact ⟨g, hlate, hRates g.native hL⟩

/-- The same statement at the requested lateness index `R`. The packet is
the producer's output at lateness `max R L0`; only its lateness certificate
`sourceData.late` is weakened from `max R L0` to `R`. The detector, state,
selector, smooth original record and nonrange proof are unchanged. -/
theorem exists_generatedStep123Output_imageErrors_cofinal_atLateness :
    ∃ L0 : ℝ, 4 ≤ L0 ∧
      ∀ (ρ : zetaZeroConfig.carrier) {β : ℝ}
        (_hβ : 0 < β) (_hβρ : β < |(ρ : ℂ).re - 1 / 2|)
        (σ : ReversalParity) (R : ℝ),
        ∃ g : GeneratedStep123Output ρ β σ R,
          max R L0 < fixedOriginalSincTrialAperture g.sourceData.separation ∧
          originalDetectorPhysicalH1Error
              (finitePhysicalSynthesis
                (fixedOriginalSincTrialAperture g.sourceData.separation)
                (originalDetectorQuarticCutoff
                  (fixedOriginalSincTrialAperture g.sourceData.separation))
                (canonicalNativeCoefficientInclusion σ
                  (fixedOriginalSincTrialAperture g.sourceData.separation)
                  (originalDetectorQuarticCutoff
                    (fixedOriginalSincTrialAperture g.sourceData.separation))
                  g.native.retained.state.detector))
              g.native.originalTrial ≤
            (fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale
                  (fixedOriginalSincTrialAperture g.sourceData.separation)) ∧
          nativePhysicalH1Norm g.native.physicalSourceError ≤
            (fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale
                  (fixedOriginalSincTrialAperture g.sourceData.separation)) ∧
          |(inner ℂ (nativePoleNeutralParityCanonical σ
                (fixedOriginalSincTrialAperture g.sourceData.separation)
                (originalDetectorQuarticCutoff
                  (fixedOriginalSincTrialAperture g.sourceData.separation))
                g.native.retained.state.detector) g.native.retained.state.detector).re -
              (zetaZeroConfig.W g.native.originalTrial g.native.originalTrial).re| ≤
            (1 + fixedOriginalSincTrialAperture g.sourceData.separation) *
              (fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
              Real.exp (fixedOriginalSincTrialAperture g.sourceData.separation / 2 -
                originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                  originalDetectorQuarticRootScale
                    (fixedOriginalSincTrialAperture g.sourceData.separation)) := by
  obtain ⟨L0, hL0, hRates⟩ := step123NativeOutput_imageErrors_commonThreshold
  refine ⟨L0, hL0, ?_⟩
  intro ρ β hβ hβρ σ R
  obtain ⟨g⟩ := exists_generatedStep123Output ρ hβ hβρ σ (max R L0)
  have hlate : max R L0 < fixedOriginalSincTrialAperture g.sourceData.separation :=
    (le_max_left _ 4).trans_lt g.native_aperture_bound
  have hL : L0 ≤ fixedOriginalSincTrialAperture g.sourceData.separation :=
    ((le_max_right R L0).trans_lt hlate).le
  have hR : max R 4 < fixedOriginalSincTrialAperture g.sourceData.separation :=
    (max_le_max (le_max_left R L0) le_rfl).trans_lt g.native_aperture_bound
  let d : OriginalDetectorPaddedFinitePhaseData β
      (nativeOriginalDetectorPhaseSign σ) R :=
    { separation := g.sourceData.separation
      aperture_pos := g.sourceData.aperture_pos
      separation_gt_scale := g.sourceData.separation_gt_scale
      late := hR
      image_threshold_paid := g.sourceData.image_threshold_paid
      unit := g.sourceData.unit
      depth := g.sourceData.depth
      original_depth := g.sourceData.original_depth }
  let g' : GeneratedStep123Output ρ β σ R :=
    { beta_pos := g.beta_pos
      beta_below := g.beta_below
      sourceData := d
      native := g.native
      native_aperture_bound := hR
      offLine := g.offLine
      true_input_nonrange := g.true_input_nonrange }
  exact ⟨g', hlate, hRates g.native hL⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.CCM.Step123NativeOutput.detectorCoefficients_eq_paddedUnit
#print axioms Zeta23.CCM.Step123NativeOutput.detectorNativeEnergy_eq_paddedNativeEnergy
#print axioms Zeta23.CCM.Step123NativeOutput.physicalSourceError_eq_storedDetector
#print axioms Zeta23.CCM.Step123NativeOutput.physicalFiniteImage_ae_eq_paddedUnit
#print axioms Zeta23.CCM.step123NativeOutput_imageErrors_commonThreshold
#print axioms Zeta23.CCM.step123NativeOutput_imageErrors_at_sourceThreshold
#print axioms Zeta23.ExceptionalZero.exists_generatedStep123Output_imageErrors_cofinal
#print axioms Zeta23.ExceptionalZero.exists_generatedStep123Output_imageErrors_cofinal_atLateness
