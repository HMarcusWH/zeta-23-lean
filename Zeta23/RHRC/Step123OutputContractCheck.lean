import Zeta23.CCM.Step123NativeSourceSpectralEvidence
import Zeta23.ExceptionalZero.Step4OutputSufficiency
import Zeta23.CCM.PoleNeutralCompactInverse
import Zeta23.CCM.Step123PhysicalImageIdentity
import Zeta23.CCM.OriginalDetectorPaddedPhaseScalar
import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.ExceptionalZero.Step123CompleteOutput

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

open MeasureTheory Set
namespace Zeta23.RHRC
open Zeta23.CCM Zeta23.ExceptionalZero

/-- MC01. The unchanged fixed source has positivity, exact compact support,
reflection symmetry, unit mass, and its actual paper Fourier transform. -/
theorem mc01_source_mass_one {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    (∀ x : ℝ, 0 ≤ universalSincSource UniversalSinc.fixedScale x) ∧
    tsupport (universalSincSource UniversalSinc.fixedScale) ⊆
      Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale ∧
    Function.Even (universalSincSource UniversalSinc.fixedScale) ∧
    (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1 ∧
    Zeta23.paperFT
      (fun x : ℝ => (universalSincSource UniversalSinc.fixedScale x : ℂ)) =
      UniversalSinc.product UniversalSinc.fixedScale :=
  (Step123NativeSourceSpectralEvidence.fromNative out).source_fixed

/-- MC02. Actual zero-indexed cofinal detector, one phase at a time: the
COMPLETE N01-N40 + G01-G04 output exists beyond `max R 4` and beyond the
common same-state threshold. -/
theorem mc02_original_detector_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123CompleteOutput ρ β σ R,
      max R 4 < fixedOriginalSincTrialAperture out.generated.sourceData.separation ∧
      max R step123SameStateThreshold <
        fixedOriginalSincTrialAperture out.generated.sourceData.separation := by
  obtain ⟨out⟩ := exists_generatedStep123CompleteOutput ρ hβ hβρ σ R
  exact ⟨out, out.generated.native_aperture_bound, out.thresholds_paid⟩

/-- MC03. The one finite image has unit norm, EXACT normalized physical
realization, and both native pole moments. The original smooth trial is
not substituted for this finite image. -/
theorem mc03_physical_finite_image_unit {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    (‖out.physicalFiniteImage‖ = 1) ∧
    (finitePhysicalSynthesis
      (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (canonicalNativeCoefficientInclusion σ
        (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector) =
      originalDetectorPaddedFinitePhysicalUnit
        (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos) ∧
    (canonicalPoleEvenFunctional (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (nativePoleNeutralParityAmbient σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector) = 0 ∧
     canonicalPoleOddFunctional (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (nativePoleNeutralParityAmbient σ (fixedOriginalSincTrialAperture a)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector) = 0) :=
  ⟨out.physicalFiniteImage_unit,
   out.finitePhysicalSource_eq_originalPadded,
   out.originalDetector_poles⟩

/-- MC04. The literal source selector coexists with the shared two-phase
positive denominator threshold, full real circulant Gram/energy matrices,
and exact scalar phase quotient. None is supplied by the caller as a bridge. -/
theorem mc04_actual_selector {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    AdmissibleDetectorSelector β (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.eta out.retained.state.selection.cutoff ∧
    (∃ L0 : ℝ, 2 ≤ L0 ∧
      ∀ (a : ℝ) (ha : UniversalSinc.fixedScale < a)
        (hL : 0 < fixedOriginalSincTrialAperture a),
        L0 ≤ fixedOriginalSincTrialAperture a →
        (0 < originalDetectorPaddedPhaseNu (fixedOriginalSincTrialAperture a)
          fixedOriginalSincLobeCenter hL +
          originalDetectorPaddedPhaseOmega (fixedOriginalSincTrialAperture a)
          fixedOriginalSincLobeCenter hL) ∧
        (0 < originalDetectorPaddedPhaseNu (fixedOriginalSincTrialAperture a)
          fixedOriginalSincLobeCenter hL -
          originalDetectorPaddedPhaseOmega (fixedOriginalSincTrialAperture a)
          fixedOriginalSincLobeCenter hL)) ∧
    (∀ (L c : ℝ) (hL : 0 < L),
      originalDetectorPaddedFinitePhaseGram L c hL =
        !![(originalDetectorPaddedPhaseNu L c hL : ℂ),
          (originalDetectorPaddedPhaseOmega L c hL : ℂ);
          (originalDetectorPaddedPhaseOmega L c hL : ℂ),
          (originalDetectorPaddedPhaseNu L c hL : ℂ)]) ∧
    (∀ (L c : ℝ) (hL : 0 < L),
      originalDetectorPaddedFinitePhaseNativeEnergy L c hL =
        !![(originalDetectorPaddedPhaseD L c hL : ℂ),
          (originalDetectorPaddedPhaseC L c hL : ℂ);
          (originalDetectorPaddedPhaseC L c hL : ℂ),
          (originalDetectorPaddedPhaseD L c hL : ℂ)]) ∧
    (∀ (phase : ℝ) (hphase : phase = 1 ∨ phase = -1)
      (L c : ℝ) (hL : 0 < L),
      (inner ℂ ((canonicalSourceMatrix L (originalDetectorQuarticCutoff L)).toEuclideanLin
        (originalDetectorPaddedFinitePhaseVector phase L c hL))
        (originalDetectorPaddedFinitePhaseVector phase L c hL)).re /
        ‖originalDetectorPaddedFinitePhaseVector phase L c hL‖ ^ 2 =
      (originalDetectorPaddedPhaseD L c hL +
        phase * originalDetectorPaddedPhaseC L c hL) /
      (originalDetectorPaddedPhaseNu L c hL +
        phase * originalDetectorPaddedPhaseOmega L c hL)) := by
  refine ⟨out.source_selector, exists_originalDetectorPaddedPhase_positive_denominators,
    ?_, ?_, ?_⟩
  · intro L c hL
    exact originalDetectorPaddedPhaseGram_real L c hL
  · intro L c hL
    exact originalDetectorPaddedPhaseEnergy_real L c hL
  · intro phase hphase L c hL
    exact originalDetectorPaddedPhase_scalar_quotient hphase L c hL

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
        (canonicalPoleNeutralTrialChannel σ L Kd i) p) ∧
    out.OriginalDetectorAmbientResiduals := by
  let evidence := Step123NativeSourceSpectralEvidence.fromNative out
  exact ⟨evidence.variance, evidence.gram, evidence.channels,
    out.n38_forcing_ambient_residuals⟩

/-- MC08. The selected ground has its own true eigenpair, and the actual
cutoff bottoms admit the exhaustive even/odd/tie trichotomy WITH every
branch's consequences instantiated on the stored selected ground and the
stored `lam` (N21), for the actual branch and for every value of the
existing neutral-bottom tag. -/
def mc08_selected_ground_consumer {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    (‖out.selectedGround‖ = 1 ∧
      nativePoleNeutralParityCanonical out.retained.state.selectedParity
        (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.selectedGround =
        (out.retained.state.selection.lam : ℂ) • out.selectedGround) ∧
    Nonempty (PoleNeutralGroundBranch
      (fixedOriginalSincTrialAperture a)
      out.retained.state.selection.cutoff
      out.aperture_pos out.source_selector.cutoff_nonempty) ∧
    DetectorRetainedSelectedGroundBranch out.retained.state ∧
    (∀ b : PoleNeutralGroundBranch (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty,
      out.retained.state.groundBranchFacts b) :=
  ⟨(Step123NativeSourceSpectralEvidence.fromNative out).selected_eigenvector,
    poleNeutralGround_branch_exhaustive out.aperture_pos
      out.retained.state.selection.cutoff out.source_selector.cutoff_nonempty,
    out.n21_retained_branch,
    out.n21_groundBranch_facts⟩

/-- MC09. The genuine supported compact inverse has a unique H2
solution, actual support, and sharp norm-four estimate on its exact
finite-source hypothesis class. Binding it to the selected physical
forcing is separately audited, not assumed. -/
def mc09_compact_inverse_consumer {β a : ℝ} {σ : ReversalParity}
    (_out : Step123NativeOutput β σ a)
    {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Set.Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    (∃! u : NativeCompactPoleH2 s f, True) ∧
    (tsupport (nativePoleCompactH2 hs hf hsupport hplus hminus).value ⊆
      Icc (-s) s) ∧
    ((eLpNorm (nativePoleCompactH2 hs hf hsupport hplus hminus).value
      2 volume).toReal ≤ 4 * (eLpNorm f 2 volume).toReal) :=
  ⟨poleNeutral_compactInverse_exists_unique hs hf hsupport hplus hminus,
   poleNeutral_compactInverse_support hs hf hsupport hplus hminus,
   poleNeutral_compactInverse_norm_bound hs hf hsupport hplus hminus⟩

/-- MC10. Source-specific signed four-history transfer at the actual phase
and normalization, not a prime-only or reflected-term-free surrogate. -/
def mc10_original_four_history_consumer {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    (∀ {s : ℝ} {f : ℝ → ℂ} (u : NativeCompactPoleH2 s f),
      Continuous f →
      (∫ x in (-s)..s, f x * out.smoothOriginal.primeHistories x) =
        ∫ x in (-s)..s, u.value x *
          originalSmoothFourPrimeXHistories
            (nativeOriginalDetectorPhaseSign σ) a x) ∧ out.ForcingSourceChannels :=
  ⟨(Step123OriginalBoundaryEvidence.fromNative out).original_signed_four_histories_actual_X,
    out.n36_forcingSourceChannels⟩

/-- MC11. Quantified actual projected source error, rather than an opaque
evidence-record return or an unsupported global Schur upper estimate. -/
def mc11_source_error_consumer {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    (∃ C_Q : ℝ, 0 < C_Q ∧
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
            nativePhysicalH1Norm out.physicalSourceError * ‖v‖) ∧
    Step123ForcingErrorRates out :=
  ⟨(Step123OriginalBoundaryEvidence.fromNative out).actual_quantified_projected_forcing_error,
    step123ForcingErrorRates_of_threshold out out.image_threshold_paid.le⟩

/-- MC12. The original exterior object is canonical, retains the
interior restriction without a zero-contact assumption, and carries
the exact full response plus all prime histories. -/
theorem mc12_original_exterior_is_canonical {β a : ℝ} {σ : ReversalParity}
    (out : Step123NativeOutput β σ a) :
    (¬ (out.smoothOriginal.interior =ᵐ[volume] (0 : ℝ → ℂ))) ∧
    (out.smoothOriginal =
      OriginalNativeExteriorRecord.fromOriginalSource
        (nativeOriginalDetectorPhaseSign σ) a out.aperture_pos) ∧
    (∀ x : ℝ, out.smoothOriginal.response x =
      out.smoothOriginal.left x + out.smoothOriginal.interior x +
        out.smoothOriginal.right x) ∧
    (MemLp out.smoothOriginal.interior 2 volume) ∧
    (∀ x : ℝ,
      nativeWeilPrimeResponse out.originalTrial x =
        out.smoothOriginal.primeHistories x) :=
  ⟨out.originalInterior_not_ae_zero, out.smoothOriginal_eq, out.smoothOriginal.reconstruction,
   out.smoothOriginal.interior_memLp, out.smoothOriginal.prime_eq⟩

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

/-- MC14. From ONE actual generated output, build the COMPLETE N01-N40
native record on that same native packet (the returned record's packet is
literally `out.native`), together with the earlier source/spectral,
arithmetic/range and exterior evidence chain on the same output.  No
caller-supplied bridge is used. -/
def mc14_one_source_full_consumer
    {ρ : zetaZeroConfig.carrier} {β : ℝ}
    {σ : ReversalParity} {R : ℝ}
    (out : GeneratedStep123Output ρ β σ R) :
    { c : Step123CompleteNativeOutput β σ out.sourceData.separation //
        c.native = out.native } ×
      GeneratedStep123ComposedEvidencePacket ρ β σ R :=
  (⟨Step123CompleteNativeOutput.ofNative out.native, rfl⟩,
    GeneratedStep123ComposedEvidencePacket.fromIntegrated
      (GeneratedStep123IntegratedPacket.fromActualBoundary
        (GeneratedStep123BoundaryPacket.fromActualGenerated out)))

/-- MC15. Each phase separately has arbitrarily late COMPLETE outputs.
No all-large-aperture or common-both-parities upgrade is asserted. -/
theorem mc15_every_phase_separately_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|) :
    ∀ (σ : ReversalParity) (R : ℝ),
      ∃ out : GeneratedStep123CompleteOutput ρ β σ R,
        max R 4 < fixedOriginalSincTrialAperture out.generated.sourceData.separation ∧
        max R step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation := by
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
