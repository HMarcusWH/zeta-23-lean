import Zeta23.CCM.NativeCausalAdjointZeroJets

/-!
# The actual causal witness separates the actual stable input from the range

The moment hypotheses are literal integrals of the fixed kernel and input.
They are not accepted as an off-line zeta-zero theorem: the analytic zeta
and source-jet identities must independently discharge these hypotheses.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

theorem nativeCausalExponentialWitness_annihilates_rangeClosure_of_kernel_moments
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (hzero : ∀ j ≤ k, nativeCompletionKernelLaplaceMoment epsilon w j = 0)
    {f : nativeCompletionCausalL2}
    (hf : f ∈ closure (Set.range (nativeDampedCompletionCausalL2Operator epsilon hepsilon))) :
    inner ℂ (nativeCausalExponentialWitness w hw k) f = 0 := by
  have hc : IsClosed {g : nativeCompletionCausalL2 |
      inner ℂ (nativeCausalExponentialWitness w hw k) g = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hr : Set.range (nativeDampedCompletionCausalL2Operator epsilon hepsilon) ⊆
      {g | inner ℂ (nativeCausalExponentialWitness w hw k) g = 0} := by
    rintro g ⟨x, rfl⟩
    exact nativeCausalExponentialWitness_annihilates_range_of_kernel_moments
      epsilon hepsilon w hw k hzero x
  exact closure_minimal hr hc hf

theorem nativeCompletedInput_not_mem_rangeClosure_of_moments
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (hzero : ∀ j ≤ k, nativeCompletionKernelLaplaceMoment epsilon w j = 0)
    (hinput : nativeCausalLaplaceMoment w k
      (nativeCompletedInputCausalL2 epsilon hepsilon : NativeCompletionL2) ≠ 0) :
    nativeCompletedInputCausalL2 epsilon hepsilon ∉
      closure (Set.range (nativeDampedCompletionCausalL2Operator epsilon hepsilon)) := by
  intro hf
  apply hinput
  rw [← nativeCausalExponentialWitness_inner_eq_laplaceMoment w hw k]
  exact nativeCausalExponentialWitness_annihilates_rangeClosure_of_kernel_moments
    epsilon hepsilon w hw k hzero hf

/-- A nonzero actual input jet also gives a quantitative lower bound for
every actual range residual, with the unnormalized witness norm paid. -/
theorem nativeCompletedInput_rangeResidual_lower_of_moments
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (hzero : ∀ j ≤ k, nativeCompletionKernelLaplaceMoment epsilon w j = 0)
    (f : nativeCompletionCausalL2) :
    ‖nativeCausalLaplaceMoment w k
      (nativeCompletedInputCausalL2 epsilon hepsilon : NativeCompletionL2)‖ ≤
      ‖nativeCausalExponentialWitness w hw k‖ *
        ‖nativeCompletedInputCausalL2 epsilon hepsilon -
          nativeDampedCompletionCausalL2Operator epsilon hepsilon f‖ := by
  have hi : inner ℂ (nativeCausalExponentialWitness w hw k)
      (nativeCompletedInputCausalL2 epsilon hepsilon -
        nativeDampedCompletionCausalL2Operator epsilon hepsilon f) =
      nativeCausalLaplaceMoment w k
        (nativeCompletedInputCausalL2 epsilon hepsilon : NativeCompletionL2) := by
    rw [inner_sub_right,
      nativeCausalExponentialWitness_annihilates_range_of_kernel_moments
        epsilon hepsilon w hw k hzero f, sub_zero,
      nativeCausalExponentialWitness_inner_eq_laplaceMoment]
  rw [← hi]
  exact norm_inner_le_norm _ _

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCausalExponentialWitness_annihilates_rangeClosure_of_kernel_moments
#print axioms Zeta23.CCM.nativeCompletedInput_not_mem_rangeClosure_of_moments
#print axioms Zeta23.CCM.nativeCompletedInput_rangeResidual_lower_of_moments
