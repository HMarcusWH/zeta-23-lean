import Zeta23.CCM.NativeCausalLaplaceDerivatives
import Zeta23.CCM.NativeCausalAdjointZeroJets

/-!
# Literal floor-kernel Laplace derivatives

The fixed damped floor kernel itself has a genuine causal L2 class. Its
literal integral moments therefore inherit all derivative signs and order
criteria from the actual causal L2 Laplace theorem.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

theorem nativeDampedCompletionKernel_le_one {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (t : ℝ) :
    nativeDampedCompletionKernel epsilon t ≤ 1 := by
  by_cases ht : 0 ≤ t
  · exact ((nativeDampedCompletionKernel_le_native hepsilon t).trans
      (nativePositiveCompletion_le_exp t)).trans
      (Real.exp_le_one_iff.mpr (by linarith))
  · rw [nativeDampedCompletionKernel_zero_of_neg epsilon (lt_of_not_ge ht)]
    norm_num

theorem nativeDampedCompletionKernel_complex_memLp_two {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    MemLp (fun t : ℝ => (nativeDampedCompletionKernel epsilon t : ℂ)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (nativeDampedCompletionKernel_measurable epsilon).complex_ofReal.aestronglyMeasurable).mpr
  apply (nativeDampedCompletionKernel_integrable hepsilon).mono'
    (((nativeDampedCompletionKernel_measurable epsilon).complex_ofReal.aestronglyMeasurable).norm.pow 2)
  filter_upwards with t
  change ‖‖(nativeDampedCompletionKernel epsilon t : ℂ)‖ ^ 2‖ ≤
    nativeDampedCompletionKernel epsilon t
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real,
    Real.norm_of_nonneg (nativeDampedCompletionKernel_nonneg epsilon t)]
  nlinarith [nativeDampedCompletionKernel_nonneg epsilon t,
    nativeDampedCompletionKernel_le_one hepsilon t]

def nativeDampedCompletionKernelL2 (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) : NativeCompletionL2 :=
  (nativeDampedCompletionKernel_complex_memLp_two hepsilon).toLp
    (fun t : ℝ => (nativeDampedCompletionKernel epsilon t : ℂ))

theorem nativeDampedCompletionKernelL2_coeFn (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeDampedCompletionKernelL2 epsilon hepsilon =ᵐ[volume]
      fun t : ℝ => (nativeDampedCompletionKernel epsilon t : ℂ) :=
  (nativeDampedCompletionKernel_complex_memLp_two hepsilon).coeFn_toLp

theorem nativeDampedCompletionKernelL2_causal (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeDampedCompletionKernelL2 epsilon hepsilon ∈ nativeCompletionCausalL2 := by
  filter_upwards [nativeDampedCompletionKernelL2_coeFn epsilon hepsilon] with t ht
  intro hneg
  rw [ht, nativeDampedCompletionKernel_zero_of_neg epsilon hneg, Complex.ofReal_zero]

def nativeDampedCompletionKernelCausalL2 (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeCompletionCausalL2 :=
  ⟨nativeDampedCompletionKernelL2 epsilon hepsilon,
    nativeDampedCompletionKernelL2_causal epsilon hepsilon⟩

theorem nativeCompletionKernelLaplaceMoment_eq_causalMoment
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (k : ℕ) :
    nativeCompletionKernelLaplaceMoment epsilon w k =
      nativeCausalLaplaceMoment w k (nativeDampedCompletionKernelCausalL2 epsilon hepsilon :
        NativeCompletionL2) := by
  unfold nativeCompletionKernelLaplaceMoment nativeCausalLaplaceMoment
  apply integral_congr_ae
  filter_upwards [nativeDampedCompletionKernelL2_coeFn epsilon hepsilon] with t ht
  change _ = (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) *
    nativeDampedCompletionKernelL2 epsilon hepsilon t
  rw [ht]
  ring

theorem nativeCompletionKernelLaplace_analyticAt
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) :
    AnalyticAt ℂ (fun z : ℂ => nativeCompletionKernelLaplaceMoment epsilon z 0) w := by
  have heq : (fun z : ℂ => nativeCompletionKernelLaplaceMoment epsilon z 0) =
      fun z : ℂ => nativeCausalLaplaceMoment z 0
        (nativeDampedCompletionKernelCausalL2 epsilon hepsilon : NativeCompletionL2) := by
    funext z
    exact nativeCompletionKernelLaplaceMoment_eq_causalMoment epsilon hepsilon z 0
  rw [heq]
  exact nativeCausalLaplaceMoment_analyticAt w hw 0 _

theorem nativeCompletionKernelLaplace_iteratedDeriv
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => nativeCompletionKernelLaplaceMoment epsilon z 0) w =
      (-1 : ℂ) ^ k * nativeCompletionKernelLaplaceMoment epsilon w k := by
  have heq : (fun z : ℂ => nativeCompletionKernelLaplaceMoment epsilon z 0) =
      fun z : ℂ => nativeCausalLaplaceMoment z 0
        (nativeDampedCompletionKernelCausalL2 epsilon hepsilon : NativeCompletionL2) := by
    funext z
    exact nativeCompletionKernelLaplaceMoment_eq_causalMoment epsilon hepsilon z 0
  rw [heq, nativeCausalLaplaceMoment_iteratedDeriv w hw k,
    ← nativeCompletionKernelLaplaceMoment_eq_causalMoment epsilon hepsilon w k]

theorem nativeCompletionKernelLaplaceMoment_vanishes_below_analyticOrder
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (n : ℕ)
    (horder : (n : ℕ∞) ≤ analyticOrderAt
      (fun z : ℂ => nativeCompletionKernelLaplaceMoment epsilon z 0) w) :
    ∀ k < n, nativeCompletionKernelLaplaceMoment epsilon w k = 0 := by
  have h := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (nativeCompletionKernelLaplace_analyticAt epsilon hepsilon w hw)).mp horder
  intro k hk
  have hd := h k hk
  rw [nativeCompletionKernelLaplace_iteratedDeriv epsilon hepsilon w hw k] at hd
  exact (mul_eq_zero_iff_left (pow_ne_zero k (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)))).mp hd

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDampedCompletionKernel_complex_memLp_two
#print axioms Zeta23.CCM.nativeDampedCompletionKernelL2_coeFn
#print axioms Zeta23.CCM.nativeCompletionKernelLaplaceMoment_eq_causalMoment
#print axioms Zeta23.CCM.nativeCompletionKernelLaplace_analyticAt
#print axioms Zeta23.CCM.nativeCompletionKernelLaplace_iteratedDeriv
#print axioms Zeta23.CCM.nativeCompletionKernelLaplaceMoment_vanishes_below_analyticOrder
