import Zeta23.CCM.Step123NativeSourceSpectralEvidence
import Zeta23.ExceptionalZero.Step4OutputSufficiency
import Zeta23.CCM.PoleNeutralCompactInverse

/-!
# PR292: typed source-bound Step 1-3 consumer checks

These sixteen declarations force Lean to consume the ACTUAL source-bound
constructors and their dependent fields, rather than searching for theorem
names. The structured consumer is built from one generated detector and
one retained selection, never from a second chosen ground.

IMPORTANT: These are typed interface checks. They do not substitute for
the separately mandated N01-N40/G01-G04 independent semantic reviews,
the 99-export compiler/axiom audit, D2, or the missing Step 4 antecedents.
-/

noncomputable section

open MeasureTheory
namespace Zeta23.RHRC
open Zeta23.CCM Zeta23.ExceptionalZero

/-- MC01. This is the actual infinite-convolution source, not a fit. -/
theorem mc01_source_mass_one {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1 :=
  out.originalSource_mass_one

/-- MC02. Actual zero-indexed cofinal detector, one phase at a time. -/
theorem mc02_original_detector_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123ComposedEvidencePacket ρ β σ R,
      max R 4 < fixedOriginalSincTrialAperture
        out.integrated.boundary.generated.sourceData.separation :=
  exists_generatedStep123ComposedEvidencePacket_cofinal ρ hβ hβρ σ R

/-- MC03. The finite image, not the original smooth test, is unit norm. -/
theorem mc03_physical_finite_image_unit {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    ‖out.physicalFiniteImage‖ = 1 :=
  out.physicalFiniteImage_unit

/-- MC04. The genuine selected admissibility witness is retained. -/
theorem mc04_actual_selector {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    AdmissibleDetectorSelector β (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.eta out.retained.state.selection.cutoff :=
  out.source_selector

/-- MC05. The only retained state is the original producer's state. -/
def mc05_single_retained_state {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    Step123NativeCorePacket σ
      (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (Real.exp (β * fixedOriginalSincTrialAperture a))
      out.aperture_pos :=
  out.retained

/-- MC06. Both exact inverse inequalities, with distinct shifts and constants.
The detector predecessor is evaluated at -eta, the selected-ground one at lambda. -/
def mc06_two_inverse_budget_consumer {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    let state := out.retained.state
    (‖(nativeDetectorPredecessorEquiv σ state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      12 * ((originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture a) - 1 : ℕ) : ℝ) /
        Real.exp (β * fixedOriginalSincTrialAperture a)) ∧
    (‖(nativeSelectedGroundPredecessorEquiv
        state.selectedParity state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      6 * ((originalDetectorQuarticCutoff
        (fixedOriginalSincTrialAperture a) - 1 : ℕ) : ℝ) /
        Real.exp (β * fixedOriginalSincTrialAperture a)) := by
  let evidence := Step123NativeSourceSpectralEvidence.fromNative out
  exact ⟨evidence.detector_inverse, evidence.selected_inverse⟩

/-- MC07. Same original detector, full neutral variance, Gram and channel identities. -/
def mc07_neutral_channel_consumer {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    let L := fixedOriginalSincTrialAperture a
    let Kd := originalDetectorQuarticCutoff L
    let p := out.retained.state.detector
    (‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (inner ℂ p (nativePoleNeutralParityCanonical σ L Kd
        (nativePoleNeutralParityCanonical σ L Kd p))).re -
      canonicalPoleNeutralTrialRayleigh σ L Kd p ^ 2) ∧
    (‖canonicalPoleNeutralTrialResidual σ L Kd p‖ ^ 2 =
      (∑ i, ∑ j,
        canonicalPoleNeutralTrialChannelGram σ L Kd p i j).re) ∧
    (canonicalPoleNeutralTrialResidual σ L Kd p =
      ∑ i, nativeTrialResidual
        (canonicalPoleNeutralTrialChannel σ L Kd i) p) := by
  let evidence := Step123NativeSourceSpectralEvidence.fromNative out
  exact ⟨evidence.variance, evidence.gram, evidence.channels⟩

/-- MC08. The actual stored selected ground has unit norm and its own
eigen-equation. Branch-exhaustive ties remain a separate MC08 check. -/
def mc08_selected_ground_consumer {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    ‖out.selectedGround‖ = 1 ∧
    nativePoleNeutralParityCanonical out.retained.state.selectedParity
      (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.cutoff out.selectedGround =
      (out.retained.state.selection.lam : ℂ) • out.selectedGround :=
  (Step123NativeSourceSpectralEvidence.fromNative out).selected_eigenvector

/-- MC09. Consume the actual compact H2 existence/uniqueness theorem.
Instantiating the actual selected finite physical test is a further obligation. -/
def mc09_compact_inverse_consumer {β a : ℝ} {σ : ReversalParity}
    (_out : Step123NativeOutput β σ a)
    {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Set.Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    ∃! u : NativeCompactPoleH2 s f, True :=
  poleNeutral_compactInverse_exists_unique hs hf hsupport hplus hminus

/-- MC10. Source-specific signed four-history transfer at the actual phase
and normalization, not a prime-only or reflected-term-free surrogate. -/
def mc10_original_four_history_consumer {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    ∀ {s : ℝ} {f : ℝ → ℂ} (u : NativeCompactPoleH2 s f),
      Continuous f →
      (∫ x in (-s)..s, f x * out.smoothOriginal.primeHistories x) =
        ∫ x in (-s)..s, u.value x *
          originalSmoothFourPrimeXHistories
            (nativeOriginalDetectorPhaseSign σ) a x :=
  (Step123OriginalBoundaryEvidence.fromNative out).original_signed_four_histories_actual_X

/-- MC11. Quantified actual projected source error, rather than an opaque
evidence-record return or an unsupported global Schur upper estimate. -/
def mc11_source_error_consumer {β a : ℝ} {σ : ReversalParity}
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
            nativePhysicalH1Norm out.physicalSourceError * ‖v‖ :=
  (Step123OriginalBoundaryEvidence.fromNative out).actual_quantified_projected_forcing_error

/-- MC12. Original right exterior and generally nonzero interior remain. -/
theorem mc12_original_exterior_is_canonical {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    out.smoothOriginal =
      OriginalNativeExteriorRecord.fromOriginalSource
        (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos :=
  out.smoothOriginal_eq

/-- MC13. The actual zeta-zero-dependent causal nonrange obstruction. -/
theorem mc13_actual_input_nonrange
    {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {σ : ReversalParity} {R : ℝ}
    (out : GeneratedStep123Output ρ β σ R) :
    nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
      (nativeZeroJetDamping_pos ρ out.offLine).le ∉
        closure (Set.range (nativeDampedCompletionCausalL2Operator
          (nativeZeroJetDamping ρ) (nativeZeroJetDamping_pos ρ out.offLine).le)) :=
  out.true_input_nonrange

/-- MC14. Compose source/spectral, arithmetic/range and exterior views from
ONE actual generated output, with no caller-supplied missing bridge. -/
def mc14_one_source_full_consumer
    {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {σ : ReversalParity} {R : ℝ}
    (out : GeneratedStep123Output ρ β σ R) :
    GeneratedStep123ComposedEvidencePacket ρ β σ R :=
  GeneratedStep123ComposedEvidencePacket.fromIntegrated
    (GeneratedStep123IntegratedPacket.fromActualBoundary
      (GeneratedStep123BoundaryPacket.fromActualGenerated out))

/-- MC15. No all-large-aperture or common-both-parities upgrade. -/
theorem mc15_every_phase_separately_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|) :
    ∀ (σ : ReversalParity) (R : ℝ),
      ∃ out : GeneratedStep123ComposedEvidencePacket ρ β σ R,
        max R 4 < fixedOriginalSincTrialAperture
          out.integrated.boundary.generated.sourceData.separation := by
  intro σ R
  exact mc02_original_detector_cofinal ρ hβ hβρ σ R

/-- MC16. Only the three explicit OPEN Step 4 premises suffice for RH.
The disjunction is NOT asserted to hold. -/
theorem mc16_three_conditional_cuts
    (h : NativeOriginalPrimeFieldAllDampedIntegral ∨
      NativeInputAllRangeClosure ∨
      NativeOriginalDetectorSchurSubexponential) :
    RiemannHypothesis :=
  riemannHypothesis_of_any_step4_output_cut h

end Zeta23.RHRC

#print axioms Zeta23.RHRC.mc01_source_mass_one
#print axioms Zeta23.RHRC.mc02_original_detector_cofinal
#print axioms Zeta23.RHRC.mc03_physical_finite_image_unit
#print axioms Zeta23.RHRC.mc04_actual_selector
#print axioms Zeta23.RHRC.mc05_single_retained_state
#print axioms Zeta23.RHRC.mc06_two_inverse_budget_consumer
#print axioms Zeta23.RHRC.mc07_neutral_channel_consumer
#print axioms Zeta23.RHRC.mc08_selected_ground_consumer
#print axioms Zeta23.RHRC.mc09_compact_inverse_consumer
#print axioms Zeta23.RHRC.mc10_original_four_history_consumer
#print axioms Zeta23.RHRC.mc11_source_error_consumer
#print axioms Zeta23.RHRC.mc12_original_exterior_is_canonical
#print axioms Zeta23.RHRC.mc13_actual_input_nonrange
#print axioms Zeta23.RHRC.mc14_one_source_full_consumer
#print axioms Zeta23.RHRC.mc15_every_phase_separately_cofinal
#print axioms Zeta23.RHRC.mc16_three_conditional_cuts
