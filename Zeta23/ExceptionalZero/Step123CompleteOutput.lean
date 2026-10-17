import Zeta23.CCM.Step123SameStateN38
import Zeta23.ExceptionalZero.Step123SameStateN37
import Zeta23.CCM.Step123SameStateN21
import Zeta23.CCM.Step123SameStateN23
import Zeta23.CCM.Step123SameStateN36
import Zeta23.CCM.Step123NativeFieldRecord
import Zeta23.CCM.Step123NativeSourceSpectralEvidence

/-!
# G03: the N01-N40 + G01-G04 Step 1-3 output on one retained state

`Step123CompleteNativeOutput β σ a` is the rho-free native record.  It stores
ONE `Step123NativeOutput β σ a` and two proof records about that same packet:

* `Step123NativeFieldRecord` (module `Step123NativeFieldRecord`): the 34
  contract fields N01-N13, N15-N20, N22, N24-N35, N39, N40 instantiated on the
  stored packet;
* `Step123SameStateFieldRecord` (this module): the same-state fields proved on
  the same stored detector, selected ground and source.  It currently contains
  N14, N21, N23, N36, N37 and N38.

STATUS: all forty native field slots are attached to the same packet.
This is a source implementation; independent semantic review remains open.
N39 retains the source producer's negative depth and proves that the actual
original interior is not almost everywhere zero.

N14 and N37 share the source-only threshold `step123SameStateThreshold`,
chosen before any zero, phase or packet. The original native producer pays
this threshold, so both rates are unconditional fields of the native record.

`GeneratedStep123CompleteOutput ρ β σ R` is the zero-indexed extension.  Its
only mathematical inputs are the actual zero carrier `ρ`, a horizontal
exponent `0 < β < |Re ρ - 1/2|`, the requested phase `σ` and the lateness
`R`.  It stores the generated output of the existing producer (G01 and the
native packet), both proof records about that output's native packet (G03),
the paid threshold `max R step123SameStateThreshold < L` (G02) and the
complete actual zero-jet range obstruction (G04).  Each phase is produced
separately; no common aperture for the two phases is asserted.

What is NOT proved here: no Step 4 antecedent (A-X, B-Y or C-Schur), no
Riemann hypothesis, no D2 certificate, and no independent semantic review.
Compiling this record does not set any release or review flag.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-! ## The source-only constants and one common threshold -/

/-- The source-only constant in the forcing bilinear bound, chosen before
any zero, phase or packet, together with the Weil constant and threshold. -/
def step123SameStateForcingConstant : ℝ :=
  Classical.choose step123NativeOutput_imageErrors_forcingError_at_sourceThreshold

/-- The source-only constant in the stored-shift upper bound, from the
same combined N14/N37 witness as the forcing constant and threshold. -/
def step123SameStateWeilConstant : ℝ :=
  Classical.choose
    (Classical.choose_spec step123NativeOutput_imageErrors_forcingError_at_sourceThreshold)

/-- The common source-only threshold of the same-state rates N14 and N37.
It is chosen once, from the frozen source, before any zero, phase or packet. -/
def step123SameStateThreshold : ℝ := originalDetectorPaddedImageThreshold

theorem step123SameStateForcingConstant_pos : 0 < step123SameStateForcingConstant :=
  (Classical.choose_spec (Classical.choose_spec
    step123NativeOutput_imageErrors_forcingError_at_sourceThreshold)).1

theorem step123SameStateWeilConstant_pos : 0 < step123SameStateWeilConstant :=
  (Classical.choose_spec (Classical.choose_spec
    step123NativeOutput_imageErrors_forcingError_at_sourceThreshold)).2.1

theorem four_le_step123SameStateThreshold : 4 ≤ step123SameStateThreshold :=
  four_le_originalDetectorPaddedImageThreshold

/-- N14 content at one stored packet: the physical H1 error of the stored
detector against the original smooth phase trial, the H1 norm of
`out.physicalSourceError`, and the native-form error of the stored detector,
each with its concrete quartic rate. -/
def Step123ImageErrorRates {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Prop :=
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
          originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))

/-- N14 at every stored packet beyond the common threshold. -/
theorem step123ImageErrorRates_of_threshold {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (_h : step123SameStateThreshold ≤ fixedOriginalSincTrialAperture a) :
    Step123ImageErrorRates out :=
  ((Classical.choose_spec (Classical.choose_spec
    step123NativeOutput_imageErrors_forcingError_at_sourceThreshold)).2.2 out).1

/-- N37 at the stored packet: its actual shift upper bound and both
projected forcing-error inequalities at the quartic H1 rate.  The finite
mode factor uses the predecessor dimension `K - 1`; the stored shift and
its proved upper bound remain separate summands.  This does not assert
that the composed right-hand side decays. -/
def Step123ForcingErrorRates {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Prop :=
  let L := fixedOriginalSincTrialAperture a
  let K := out.retained.state.selection.cutoff
  let Kd := originalDetectorQuarticCutoff L
  let eta := out.retained.state.selection.eta
  let rate := L ^ (17 / 2 : ℝ) *
    Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
      originalDetectorQuarticRootScale L)
  eta ≤ (step123SameStateWeilConstant / 2) * (1 + L) * Real.exp (L / 2) *
      (1 + (2 * Real.pi * Kd / L) ^ 2) ∧
  ∀ v : nativePoleNeutralParitySpace σ L (K - 1),
    ‖zetaZeroConfig.W out.physicalSourceError
        (finitePhysicalSynthesis L (K - 1)
          (canonicalNativeCoefficientInclusion σ L (K - 1) v)) +
        (eta : ℂ) * EF.weilTest out.physicalSourceError
          (finitePhysicalSynthesis L (K - 1)
            (canonicalNativeCoefficientInclusion σ L (K - 1) v)) 0‖ ≤
      (step123SameStateForcingConstant * (1 + L) * Real.exp (L / 2) *
          Real.sqrt (1 + (2 * Real.pi * (K - 1 : ℕ) / L) ^ 2) + eta) *
        rate * ‖v‖ ∧
    ‖zetaZeroConfig.W out.physicalSourceError
        (finitePhysicalSynthesis L (K - 1)
          (canonicalNativeCoefficientInclusion σ L (K - 1) v)) +
        (eta : ℂ) * EF.weilTest out.physicalSourceError
          (finitePhysicalSynthesis L (K - 1)
            (canonicalNativeCoefficientInclusion σ L (K - 1) v)) 0‖ ≤
      (step123SameStateForcingConstant * (1 + L) * Real.exp (L / 2) *
          Real.sqrt (1 + (2 * Real.pi * (K - 1 : ℕ) / L) ^ 2) +
        (step123SameStateWeilConstant / 2) * (1 + L) * Real.exp (L / 2) *
          (1 + (2 * Real.pi * Kd / L) ^ 2)) * rate * ‖v‖

/-- N37 at every stored packet beyond the same threshold as N14, with
constants fixed before any zero, phase or packet. -/
theorem step123ForcingErrorRates_of_threshold {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (_h : step123SameStateThreshold ≤ fixedOriginalSincTrialAperture a) :
    Step123ForcingErrorRates out :=
  ((Classical.choose_spec (Classical.choose_spec
    step123NativeOutput_imageErrors_forcingError_at_sourceThreshold)).2.2 out).2

/-! ## The six same-state fields on one stored packet -/

/-- The same-state fields N14, N21, N23, N36, N37 and N38 of one stored
packet.  Every field concerns the packet's own stored detector, selected
ground, selection and source; nothing is supplied by a caller. -/
structure Step123SameStateFieldRecord {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Prop where
  /-- N14 `image.errors`; the native source producer has paid its threshold. -/
  n14_image_errors : Step123ImageErrorRates out
  /-- N21 `retained.branch`: the trichotomy of the actual neutral bottoms at
  the stored aperture and selected cutoff, each branch carrying its facts
  about the stored selected ground and the stored `lam`. -/
  n21_retained_branch : DetectorRetainedSelectedGroundBranch out.retained.state
  /-- N23 `retained.tie`: in the genuine tie case of the actual bottoms, the
  singular-safe completion on the stored selected ground at the stored `lam`:
  both shifted kernels are nontrivial, kernel compatibility holds, and the
  positive-complement inverse keeps the kernel term.  No `S0 ≠ 0` claim. -/
  n23_retained_tie :
    poleNeutralEvenRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty =
      poleNeutralOddRayleighBottom (fixedOriginalSincTrialAperture a)
        out.retained.state.selection.cutoff out.aperture_pos
        out.retained.state.selection.cutoff_nonempty →
    PoleNeutralTieRetainedCompletion out.aperture_pos
      out.retained.state.selection.cutoff out.retained.state.selection.cutoff_nonempty
      out.retained.state.selection.lam out.retained.state.selectedParity out.selectedGround
  /-- N36 `forcing.source_channels`: on every actual predecessor test, the
  stored forcing coordinate expands into the Archimedean, pole (zero),
  four literal signed prime-history, `+eta` spectral-shift and finite
  approximation channels of the original trial, with the q*X bridge and the
  16-kappa local-X bound on the prime channel. -/
  n36_forcing_source_channels : out.ForcingSourceChannels
  /-- N38: the original detector's distinct ambient residual channels. -/
  n38_forcing_ambient_residuals : out.OriginalDetectorAmbientResiduals
  /-- N37 `forcing.error`, with the actual stored shift and predecessor
  finite-mode factor, beyond the same source-only threshold as N14. -/
  n37_forcing_error : Step123ForcingErrorRates out

/-- Every same-state field is proved from the packet alone. -/
theorem Step123SameStateFieldRecord.fromNative {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Step123SameStateFieldRecord out where
  n14_image_errors := step123ImageErrorRates_of_threshold out out.image_threshold_paid.le
  n21_retained_branch := out.n21_retained_branch
  n23_retained_tie := out.n23_retained_tie
  n36_forcing_source_channels := out.n36_forcingSourceChannels
  n38_forcing_ambient_residuals := out.n38_forcing_ambient_residuals
  n37_forcing_error := step123ForcingErrorRates_of_threshold out out.image_threshold_paid.le

/-! ## The complete rho-free native record -/

/-- The complete N01-N40 native record: ONE stored packet and the proof
records of all forty native fields about that same packet. -/
structure Step123CompleteNativeOutput (β : ℝ) (σ : ReversalParity) (a : ℝ) where
  native : Step123NativeOutput β σ a
  fields : Step123NativeFieldRecord native
  sameState : Step123SameStateFieldRecord native

/-- Every native packet extends to the complete record with no further
hypothesis. -/
def Step123CompleteNativeOutput.ofNative {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Step123CompleteNativeOutput β σ a where
  native := out
  fields := Step123NativeFieldRecord.fromNative out
  sameState := Step123SameStateFieldRecord.fromNative out

/-! ## G04: the actual zero-jet range obstruction -/

/-- G04 `generated.range_obstruction` for an actual off-line zero: the
reflected right zero, its multiplicity, the damping and transform point, the
exact Laplace order of the actual input, the adjoint witness annihilating the
actual completion range, the nonzero paired jet of the actual input `Y`, its
nonmembership in the range closure, and the positive residual lower bound.
This is a conditional obstruction attached to a hypothetical off-line zero;
it is not a statement that such a zero exists. -/
structure GeneratedStep123RangeObstruction (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1 / 2) : Prop where
  reflected_zero :
    ((nativeZeroJetRightZero ρ : ℂ) = (ρ : ℂ) ∨
        (nativeZeroJetRightZero ρ : ℂ) = 1 - (ρ : ℂ)) ∧
      1 / 2 < (nativeZeroJetRightZero ρ : ℂ).re
  multiplicity :
    zeroMult (nativeZeroJetRightZero ρ : ℂ) = zeroMult (ρ : ℂ) ∧
      1 ≤ zeroMult (ρ : ℂ)
  damping :
    0 < nativeZeroJetDamping ρ ∧
      nativeZeroJetDamping ρ < (nativeZeroJetRightZero ρ : ℂ).re - 1 / 2
  transform_point :
    0 < (nativeZeroJetParameter ρ).re ∧
      nativeZeroJetParameter ρ + (nativeZeroJetDamping ρ : ℂ) =
        (nativeZeroJetRightZero ρ : ℂ) - 1 / 2
  laplace_order :
    analyticOrderAt
        (fun z => nativeCausalLaplaceMoment z 0
          (nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
            (nativeZeroJetDamping_pos ρ hoff).le : NativeCompletionL2))
        (nativeZeroJetParameter ρ) =
      (zeroMult (ρ : ℂ) - 1 : ℕ)
  witness_annihilates_range :
    ∀ f : nativeCompletionCausalL2,
      inner ℂ (nativeZeroJetAdjointWitness ρ hoff)
          (nativeDampedCompletionCausalL2Operator (nativeZeroJetDamping ρ)
            (nativeZeroJetDamping_pos ρ hoff).le f) = 0
  input_jet_value :
    inner ℂ (nativeZeroJetAdjointWitness ρ hoff)
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
          (nativeZeroJetDamping_pos ρ hoff).le) =
      (-1 : ℂ) ^ zeroMult (ρ : ℂ) *
          nativeCompletionRationalMultiplier ((nativeZeroJetRightZero ρ : ℂ) - 1 / 2) *
        nativeOriginalSourceLaplace ((nativeZeroJetRightZero ρ : ℂ) - 1 / 2) *
      iteratedDeriv (zeroMult (ρ : ℂ)) riemannZeta (nativeZeroJetRightZero ρ : ℂ)
  input_jet_ne_zero :
    inner ℂ (nativeZeroJetAdjointWitness ρ hoff)
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
          (nativeZeroJetDamping_pos ρ hoff).le) ≠ 0
  nonrange :
    nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
        (nativeZeroJetDamping_pos ρ hoff).le ∉
      closure (Set.range (nativeDampedCompletionCausalL2Operator
        (nativeZeroJetDamping ρ) (nativeZeroJetDamping_pos ρ hoff).le))
  residual_lower :
    ∀ n : ℕ,
      0 < ‖inner ℂ (nativeZeroJetAdjointWitness ρ hoff)
            (nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
              (nativeZeroJetDamping_pos ρ hoff).le)‖ /
          ‖nativeZeroJetAdjointWitness ρ hoff‖ ∧
        ‖inner ℂ (nativeZeroJetAdjointWitness ρ hoff)
            (nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
              (nativeZeroJetDamping_pos ρ hoff).le)‖ /
          ‖nativeZeroJetAdjointWitness ρ hoff‖ ≤
        ‖nativeCompletedInputResidualIterate (nativeZeroJetDamping ρ)
          (nativeZeroJetDamping_pos ρ hoff).le n‖

/-- G04 holds for every actual off-line zero. -/
theorem GeneratedStep123RangeObstruction.ofOffLine (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1 / 2) : GeneratedStep123RangeObstruction ρ hoff where
  reflected_zero :=
    ⟨nativeZeroJetRightZero_eq_or_oneSub ρ, nativeZeroJetRightZero_re_gt_half ρ hoff⟩
  multiplicity :=
    ⟨nativeZeroJetRightZero_mult ρ, zetaZeroConfig.one_le_mult _ ρ.property⟩
  damping := ⟨nativeZeroJetDamping_pos ρ hoff, nativeZeroJetDamping_lt_centered_re ρ hoff⟩
  transform_point :=
    ⟨nativeZeroJetParameter_re_pos ρ hoff, nativeZeroJetParameter_add_damping ρ⟩
  laplace_order := by
    have h := nativeActualInputLaplace_order_of_zero (nativeZeroJetDamping ρ)
      (nativeZeroJetDamping_pos ρ hoff).le (nativeZeroJetRightZero ρ)
      (ne_of_gt (nativeZeroJetRightZero_re_gt_half ρ hoff)) (nativeZeroJetParameter ρ)
      (nativeZeroJetParameter_re_pos ρ hoff) (nativeZeroJetParameter_add_damping ρ)
    rwa [nativeZeroJetRightZero_mult] at h
  witness_annihilates_range := nativeZeroJet_annihilates_range ρ hoff
  input_jet_value := nativeCompletedInput_zeroJet_value ρ hoff
  input_jet_ne_zero := nativeCompletedInput_zeroJet_ne_zero ρ hoff
  nonrange := nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero ρ hoff
  residual_lower := nativeCompletedInput_zeroJet_residual_lower ρ hoff

/-! ## The zero-indexed complete output -/

/-- The complete generated output G01-G04 around ONE generated packet.
`generated` is the existing producer's output: it stores the actual zero
carrier and `β` gap (G01) and the native packet.  `fields` and `sameState`
are the forty native fields about that same native packet (G03).
`thresholds_paid` is G02 beyond `max R 4`: the aperture also exceeds the
common same-state threshold.  `rangeObstruction` is G04 for the stored
off-line certificate. -/
structure GeneratedStep123CompleteOutput
    (ρ : zetaZeroConfig.carrier) (β : ℝ)
    (σ : ReversalParity) (R : ℝ) where
  generated : GeneratedStep123Output ρ β σ R
  fields : Step123NativeFieldRecord generated.native
  sameState : Step123SameStateFieldRecord generated.native
  thresholds_paid :
    max R step123SameStateThreshold <
      fixedOriginalSincTrialAperture generated.sourceData.separation
  rangeObstruction : GeneratedStep123RangeObstruction ρ generated.offLine

/-- The complete native record of the generated packet (the same packet,
not a second construction). -/
def GeneratedStep123CompleteOutput.completeNative
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123CompleteOutput ρ β σ R) :
    Step123CompleteNativeOutput β σ g.generated.sourceData.separation where
  native := g.generated.native
  fields := g.fields
  sameState := g.sameState

/-- N14 holds unconditionally on the generated packet: its threshold is paid. -/
theorem GeneratedStep123CompleteOutput.imageErrors
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123CompleteOutput ρ β σ R) :
    Step123ImageErrorRates g.generated.native :=
  g.sameState.n14_image_errors

/-- N37 holds unconditionally on the generated packet: the same aperture
certificate pays the threshold shared with N14. -/
theorem GeneratedStep123CompleteOutput.forcingErrors
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123CompleteOutput ρ β σ R) :
    Step123ForcingErrorRates g.generated.native :=
  g.sameState.n37_forcing_error

/-- The earlier partial evidence chain, built on the SAME generated output. -/
def GeneratedStep123CompleteOutput.composed
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123CompleteOutput ρ β σ R) :
    GeneratedStep123ComposedEvidencePacket ρ β σ R :=
  GeneratedStep123ComposedEvidencePacket.fromIntegrated
    (GeneratedStep123IntegratedPacket.fromActualBoundary
      (GeneratedStep123BoundaryPacket.fromActualGenerated g.generated))

/-- Re-index a generated output to a smaller lateness.  Only the two
lateness certificates are weakened; the separation, unit, depth, native
packet, off-line certificate and nonrange proof are unchanged. -/
def GeneratedStep123Output.weakenLateness
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R R' : ℝ}
    (g : GeneratedStep123Output ρ β σ R') (hR : R ≤ R') :
    GeneratedStep123Output ρ β σ R :=
  have hR4 : max R 4 < fixedOriginalSincTrialAperture g.sourceData.separation :=
    (max_le_max hR le_rfl).trans_lt g.native_aperture_bound
  { beta_pos := g.beta_pos
    beta_below := g.beta_below
    sourceData :=
      { separation := g.sourceData.separation
        aperture_pos := g.sourceData.aperture_pos
        separation_gt_scale := g.sourceData.separation_gt_scale
        late := hR4
        unit := g.sourceData.unit
        depth := g.sourceData.depth
        original_depth := g.sourceData.original_depth
        image_threshold_paid := g.sourceData.image_threshold_paid }
    native := g.native
    native_aperture_bound := hR4
    offLine := g.offLine
    true_input_nonrange := g.true_input_nonrange }

/-- Every original generated output extends to the complete output without
an extra hypothesis: its source producer already paid the common threshold. -/
def GeneratedStep123CompleteOutput.fromGenerated
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123Output ρ β σ R) :
    GeneratedStep123CompleteOutput ρ β σ R where
  generated := g
  fields := Step123NativeFieldRecord.fromNative g.native
  sameState := Step123SameStateFieldRecord.fromNative g.native
  thresholds_paid := max_lt (lt_of_le_of_lt (le_max_left R 4) g.native_aperture_bound)
    g.sourceData.image_threshold_paid
  rangeObstruction := GeneratedStep123RangeObstruction.ofOffLine ρ g.offLine

/-- The original requested generated API has a canonical complete view.
No second producer call, detector, selection or mathematical input is used. -/
def GeneratedStep123Output.complete
    {ρ : zetaZeroConfig.carrier} {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (g : GeneratedStep123Output ρ β σ R) :
    GeneratedStep123CompleteOutput ρ β σ R :=
  GeneratedStep123CompleteOutput.fromGenerated g

/-- G03 producer.  For an actual zeta-zero carrier `ρ`, an exponent
`0 < β < |Re ρ - 1/2|`, a phase `σ` and a lateness `R`, the existing
source producer pays the common threshold and gives a
generated output whose aperture pays every common threshold, and it extends
to the complete N01-N40 + G01-G04 output.  No other hypothesis is used. -/
theorem exists_generatedStep123CompleteOutput
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    Nonempty (GeneratedStep123CompleteOutput ρ β σ R) := by
  obtain ⟨g⟩ := exists_generatedStep123Output ρ hβ hβρ σ R
  exact ⟨GeneratedStep123CompleteOutput.fromGenerated g⟩

/-- Each phase separately has arbitrarily late complete outputs.  No common
aperture for the two phases is asserted. -/
theorem exists_eachPhase_cofinal_generatedStep123CompleteOutput
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|) :
    ∀ (σ : ReversalParity) (R : ℝ),
      ∃ out : GeneratedStep123CompleteOutput ρ β σ R,
        max R step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation := by
  intro σ R
  obtain ⟨out⟩ := exists_generatedStep123CompleteOutput ρ hβ hβρ σ R
  exact ⟨out, out.thresholds_paid⟩

end Zeta23.ExceptionalZero

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- All forty native fields of the original requested API, about its one
stored state. The producer has already paid the N14/N37 source threshold. -/
def Step123NativeOutput.complete {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Step123CompleteNativeOutput β σ a :=
  Step123CompleteNativeOutput.ofNative out

/-- The literal arithmetic values together with their same-packet source,
divisor and response identities. The shared proof record avoids copying or
weakening the exact propositions of N01-N13,N15-N20,N22,N24-N35,N39,N40. -/
structure Step123ArithmeticView {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) where
  values : (ℝ → ℝ) × (ℝ → ℝ)
  fixed_values : values = (nativeOriginalPrimeField, nativeOriginalIntegerDrive)
  fields : Step123NativeFieldRecord out

/-- The actual input/correction values with their source, domain, transform,
causal-operator and adjoint-iteration identities on the same native packet.
The operator and its domain are the literal ones in `fields`, not inputs. -/
structure Step123RangeView {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) where
  values : (ℝ → ℝ) × (ℝ → ℝ)
  fixed_values : values = (nativeCompletedInput, nativeCompletionCorrection)
  fields : Step123NativeFieldRecord out

/-- One retained state with both Schur records, explicit branches, source
correction, residuals, forcing and original exterior. All facts refer to
`out`; the equality prevents a second selected state from being substituted. -/
structure Step123StructuralView {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) where
  retained : Step123NativeCorePacket σ
    (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    (Real.exp (β * fixedOriginalSincTrialAperture a)) out.aperture_pos
  retained_eq : retained = out.retained
  fields : Step123NativeFieldRecord out
  sameState : Step123SameStateFieldRecord out

/-- M22.02: arithmetic values and their proved source/divisor identities. -/
def Step123NativeOutput.arithmeticView {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Step123ArithmeticView out where
  values := out.arithmeticData
  fixed_values := rfl
  fields := Step123NativeFieldRecord.fromNative out

/-- M22.03: actual input/correction with domain, transform and operator data. -/
def Step123NativeOutput.rangeView {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Step123RangeView out where
  values := out.rangeData
  fixed_values := rfl
  fields := Step123NativeFieldRecord.fromNative out

/-- M22.04: the same retained state with complete structural proof views. -/
def Step123NativeOutput.structuralView {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Step123StructuralView out where
  retained := out.structuralData
  retained_eq := rfl
  fields := Step123NativeFieldRecord.fromNative out
  sameState := Step123SameStateFieldRecord.fromNative out

end Zeta23.CCM

#print axioms Zeta23.ExceptionalZero.four_le_step123SameStateThreshold
#print axioms Zeta23.ExceptionalZero.step123SameStateForcingConstant_pos
#print axioms Zeta23.ExceptionalZero.step123SameStateWeilConstant_pos
#print axioms Zeta23.ExceptionalZero.step123ImageErrorRates_of_threshold
#print axioms Zeta23.ExceptionalZero.step123ForcingErrorRates_of_threshold
#print axioms Zeta23.ExceptionalZero.Step123SameStateFieldRecord.fromNative
#print axioms Zeta23.ExceptionalZero.Step123CompleteNativeOutput.ofNative
#print axioms Zeta23.ExceptionalZero.GeneratedStep123RangeObstruction.ofOffLine
#print axioms Zeta23.ExceptionalZero.GeneratedStep123CompleteOutput.completeNative
#print axioms Zeta23.ExceptionalZero.GeneratedStep123CompleteOutput.imageErrors
#print axioms Zeta23.ExceptionalZero.GeneratedStep123CompleteOutput.forcingErrors
#print axioms Zeta23.ExceptionalZero.GeneratedStep123CompleteOutput.composed
#print axioms Zeta23.ExceptionalZero.GeneratedStep123Output.weakenLateness
#print axioms Zeta23.ExceptionalZero.GeneratedStep123CompleteOutput.fromGenerated
#print axioms Zeta23.ExceptionalZero.GeneratedStep123Output.complete
#print axioms Zeta23.CCM.Step123NativeOutput.complete
#print axioms Zeta23.CCM.Step123NativeOutput.arithmeticView
#print axioms Zeta23.CCM.Step123NativeOutput.rangeView
#print axioms Zeta23.CCM.Step123NativeOutput.structuralView
#print axioms Zeta23.ExceptionalZero.exists_generatedStep123CompleteOutput
#print axioms Zeta23.ExceptionalZero.exists_eachPhase_cofinal_generatedStep123CompleteOutput
