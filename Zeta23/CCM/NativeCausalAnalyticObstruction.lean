import Zeta23.CCM.NativeCausalKernelLaplaceDerivatives
import Zeta23.CCM.NativeCausalRangeObstruction

/-!
# The actual Laplace-order mismatch separates the actual stable input

This interface refers to the literal transforms of the actual damped
floor kernel and the independently constructed stable input. Connecting
their orders to an actual zeta zero is a separate source-specific proof.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

theorem nativeCausalExponentialWitness_mem_adjointKernel_of_analyticOrder
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (hkernel : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
      (fun z : ℂ => nativeCompletionKernelLaplaceMoment epsilon z 0) w) :
    nativeDampedCompletionCausalL2Adjoint epsilon hepsilon
      (nativeCausalExponentialWitness w hw k) = 0 := by
  apply nativeCausalExponentialWitness_mem_adjointKernel_of_kernel_moments
    epsilon hepsilon w hw k
  intro j hj
  exact nativeCompletionKernelLaplaceMoment_vanishes_below_analyticOrder
    epsilon hepsilon w hw (k + 1) hkernel j (Nat.lt_succ_of_le hj)

theorem nativeCompletedInput_not_mem_rangeClosure_of_analyticOrders
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (hkernel : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
      (fun z : ℂ => nativeCompletionKernelLaplaceMoment epsilon z 0) w)
    (hinput : analyticOrderAt (fun z : ℂ => nativeCausalLaplaceMoment z 0
      (nativeCompletedInputCausalL2 epsilon hepsilon : NativeCompletionL2)) w = k) :
    nativeCompletedInputCausalL2 epsilon hepsilon ∉
      closure (Set.range (nativeDampedCompletionCausalL2Operator epsilon hepsilon)) := by
  apply nativeCompletedInput_not_mem_rangeClosure_of_moments epsilon hepsilon w hw k
  · intro j hj
    exact nativeCompletionKernelLaplaceMoment_vanishes_below_analyticOrder
      epsilon hepsilon w hw (k + 1) hkernel j (Nat.lt_succ_of_le hj)
  · exact nativeCausalLaplaceMoment_ne_zero_at_analyticOrder w hw k
      (nativeCompletedInputCausalL2 epsilon hepsilon) hinput

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCausalExponentialWitness_mem_adjointKernel_of_analyticOrder
#print axioms Zeta23.CCM.nativeCompletedInput_not_mem_rangeClosure_of_analyticOrders
