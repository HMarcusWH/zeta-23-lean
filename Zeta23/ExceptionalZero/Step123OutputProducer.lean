import Zeta23.CCM.Step123OutputData
import Zeta23.ExceptionalZero.NativeActualInputZeroJets

/-!
# Actual zero-indexed source-bound Step 1-3 output producer

Every input is the actual zeta-zero carrier, a strictly smaller
horizontal exponent, the requested phase and a lateness bound.
We consume the existing padded producer ONE time, then bind its unique
retained state to the source, physical and spectral views.

This constructs a mathematically honest CORE generated packet; the full
44-field release and D2 gate are not silently asserted complete.
The actual native causal input nonrange proof is part of the packet,
not a caller-supplied hypothesis.
-/

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

structure GeneratedStep123Output
    (ρ : zetaZeroConfig.carrier) (β : ℝ)
    (σ : ReversalParity) (R : ℝ) where
  beta_pos : 0 < β
  beta_below : β < |(ρ : ℂ).re - 1 / 2|
  sourceData :
    OriginalDetectorPaddedFinitePhaseData β
      (nativeOriginalDetectorPhaseSign σ) R
  native : Step123NativeOutput β σ sourceData.separation
  native_aperture_bound :
    max R 4 < fixedOriginalSincTrialAperture sourceData.separation
  offLine : (ρ : ℂ).re ≠ 1 / 2
  true_input_nonrange :
    nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
      (nativeZeroJetDamping_pos ρ offLine).le ∉
        closure (Set.range (nativeDampedCompletionCausalL2Operator
          (nativeZeroJetDamping ρ) (nativeZeroJetDamping_pos ρ offLine).le))

/-- The current source-specific data, no additional detector or range
assumptions. -/
def GeneratedStep123Output.fromActualRetained
    (ρ : zetaZeroConfig.carrier) {β R : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity)
    (d : OriginalDetectorPaddedFinitePhaseData β
      (nativeOriginalDetectorPhaseSign σ) R)
    (state : DetectorRetainedSchurState σ
      (fixedOriginalSincTrialAperture d.separation)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
      (Real.exp (β * fixedOriginalSincTrialAperture d.separation))
      d.aperture_pos)
    (hdet : state.detector =
      nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
        d.two_le_aperture)
    (hsel : AdmissibleDetectorSelector β
      (fixedOriginalSincTrialAperture d.separation)
      state.selection.eta state.selection.cutoff) :
    GeneratedStep123Output ρ β σ R := by
  have hoff : (ρ : ℂ).re ≠ 1 / 2 := by
    intro h
    have hzero : |(ρ : ℂ).re - 1 / 2| = 0 := by rw [h]; norm_num
    linarith
  refine {
    beta_pos := hβ
    beta_below := hβρ
    sourceData := d
    native := Step123NativeOutput.ofRetained σ d state hdet hsel
    native_aperture_bound := d.late
    offLine := hoff
    true_input_nonrange := ?_
  }
  exact nativeCompletedInput_not_mem_rangeClosure_of_offLine_zero ρ hoff

/-- The same original physical source and one retained state are built
for each requested phase.  Every R is allowed, but the two phase
sequences need not use a common aperture. -/
theorem exists_generatedStep123Output
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    Nonempty (GeneratedStep123Output ρ β σ R) := by
  obtain ⟨d, state, hdet, hsel⟩ :=
    exists_originalDetectorPaddedPhase_admissible_retained_state
      σ ρ hβ hβρ R
  exact ⟨GeneratedStep123Output.fromActualRetained
    ρ hβ hβρ σ d state hdet hsel⟩

/-- Concrete cofinal aperture quantifier for the same actual generated
packet. No all-large-aperture or both-phase-same-L upgrade is implied. -/
theorem exists_generatedStep123Output_cofinal
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123Output ρ β σ R,
      max R 4 < fixedOriginalSincTrialAperture out.sourceData.separation := by
  obtain ⟨out⟩ := exists_generatedStep123Output ρ hβ hβρ σ R
  exact ⟨out, out.native_aperture_bound⟩

/-- Original requested zero-indexed exported name.  This refers to
the same source-bound cofinal generated core object; a fully validated
N01-N40 producer remains a separate release obligation. -/
theorem exists_step123Output_of_offLine_zero
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R : ℝ) :
    Nonempty (GeneratedStep123Output ρ β σ R) :=
  exists_generatedStep123Output ρ hβ hβρ σ R

/-- Each phase has arbitrarily late outputs, but no common aperture
or arbitrary all-large-aperture depth is asserted. -/
theorem exists_eachPhase_cofinal_step123Output
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|) :
    ∀ (σ : ReversalParity) (R : ℝ),
      ∃ out : GeneratedStep123Output ρ β σ R,
        max R 4 < fixedOriginalSincTrialAperture out.sourceData.separation := by
  intro σ R
  exact exists_generatedStep123Output_cofinal ρ hβ hβρ σ R

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_generatedStep123Output
#print axioms Zeta23.ExceptionalZero.exists_generatedStep123Output_cofinal
