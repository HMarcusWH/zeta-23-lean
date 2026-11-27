import Zeta23.RHRC.Step123CompleteOutputConsumer

/-!
Independent type challenges for the conditional native Step 1–3 producers.
A hypothetical actual off-line zero is an input to these challenges.
The direct terminal proof does not use these declarations.
-/

set_option autoImplicit false

noncomputable section

open Set
open Zeta23.CCM Zeta23.ExceptionalZero

namespace Zeta23.RHReference

/-- Step 1 reflects the supplied actual carrier zero, keeping its multiplicity. -/
theorem fingerprint
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ ζ : zetaZeroConfig.carrier,
      ((ζ : ℂ) = (ρ : ℂ) ∨ (ζ : ℂ) = 1 - (ρ : ℂ)) ∧
      1 / 2 < (ζ : ℂ).re ∧
      zeroMult (ζ : ℂ) = zeroMult (ρ : ℂ) ∧ 1 ≤ zeroMult (ρ : ℂ) := by
  have h := GeneratedStep123RangeObstruction.ofOffLine ρ hoff
  exact ⟨nativeZeroJetRightZero ρ, h.reflected_zero.1, h.reflected_zero.2,
    h.multiplicity.1, h.multiplicity.2⟩


/-- The source trial carries the requested sign and the original margin. -/
theorem fingerprint_depth
    (ρ : zetaZeroConfig.carrier) {β : ℝ} {σ : ReversalParity} {R : ℝ}
    (out : GeneratedStep123CompleteOutput ρ β σ R) :
    let a := out.generated.sourceData.separation
    let trial := fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a
    (zetaZeroConfig.W trial trial).re ≤ -4 * Real.exp (β * fixedOriginalSincTrialAperture a) :=
  out.generated.sourceData.original_depth

/-- Step 2 pays arbitrary lateness separately for each requested parity. -/
theorem no_hide (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hgap : β < |(ρ : ℂ).re - 1 / 2|) :
    ∀ (σ : ReversalParity) (R : ℝ),
      ∃ out : GeneratedStep123CompleteOutput ρ β σ R,
        max R step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation :=
  exists_eachPhase_cofinal_generatedStep123CompleteOutput ρ hβ hgap

/-- Step 3 reads error and range facts from one zero-indexed packet. -/
theorem same_state (ρ : zetaZeroConfig.carrier) {β : ℝ} {σ : ReversalParity}
    {R : ℝ} (out : GeneratedStep123CompleteOutput ρ β σ R) :
    Step123ImageErrorRates out.generated.native ∧
    Step123ForcingErrorRates out.generated.native ∧
    nativeCompletedInputCausalL2 (nativeZeroJetDamping ρ)
      (nativeZeroJetDamping_pos ρ out.generated.offLine).le ∉
        closure (Set.range (nativeDampedCompletionCausalL2Operator
          (nativeZeroJetDamping ρ) (nativeZeroJetDamping_pos ρ out.generated.offLine).le)) :=
  ⟨out.imageErrors, out.forcingErrors, out.rangeObstruction.nonrange⟩

end Zeta23.RHReference

#print axioms Zeta23.RHReference.fingerprint
#print axioms Zeta23.RHReference.fingerprint_depth
#print axioms Zeta23.RHReference.no_hide
#print axioms Zeta23.RHReference.same_state
