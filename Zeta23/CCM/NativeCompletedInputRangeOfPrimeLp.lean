import Zeta23.CCM.NativeDampedCompletionPointwiseBridge
import Zeta23.CCM.NativeCompletionEquation

/-!
# The actual prime-field L2 law implies the actual completed-input range law

The prime-field membership is the explicit A-X closing-law hypothesis. The
operator equation is derived from the pre-L2 literal a*X=Y equation and the
actual Bochner representative bridge. It is not supplied as an extra
premise. This module does not establish prime-field L2 membership.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

def nativeOriginalDampedPrimeField (epsilon t : ℝ) : ℂ :=
  ((Real.exp (-epsilon * t) * nativeOriginalPrimeField t : ℝ) : ℂ)

theorem nativeOriginalDampedPrimeField_zero_of_neg (epsilon : ℝ) {t : ℝ} (ht : t < 0) :
    nativeOriginalDampedPrimeField epsilon t = 0 := by
  rw [nativeOriginalDampedPrimeField, nativeOriginalPrimeField_zero_of_neg ht,
    mul_zero, Complex.ofReal_zero]

/-- The damped equation is paid as a literal pointwise identity before
any prime-field L2 assumption is introduced. -/
theorem nativeDampedCompletedInput_equation (epsilon t : ℝ) :
    nativeDampedCompletionPointwise epsilon (nativeOriginalDampedPrimeField epsilon) t =
      nativeDampedCompletedInput epsilon t := by
  have hpoint (s : ℝ) : (nativeDampedCompletionKernel epsilon s : ℂ) *
      nativeOriginalDampedPrimeField epsilon (t - s) =
      (Real.exp (-epsilon * t) : ℂ) *
        ((nativePositiveCompletion s * nativeOriginalPrimeField (t - s) : ℝ) : ℂ) := by
    have he : Real.exp (-epsilon * s) * Real.exp (-epsilon * (t - s)) =
        Real.exp (-epsilon * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold nativeDampedCompletionKernel nativeOriginalDampedPrimeField
    simp only [← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    calc
      _ = (Real.exp (-epsilon * s) * Real.exp (-epsilon * (t - s))) *
          (nativePositiveCompletion s * nativeOriginalPrimeField (t - s)) := by
        ring
      _ = _ := by rw [he]
  unfold nativeDampedCompletionPointwise
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul,
    integral_complex_ofReal, nativeCompletedInput_equation]
  exact (Complex.ofReal_mul _ _).symm

def nativeOriginalDampedPrimeFieldL2 (epsilon : ℝ)
    (hX : MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume) : NativeCompletionL2 :=
  hX.toLp (nativeOriginalDampedPrimeField epsilon)

theorem nativeOriginalDampedPrimeFieldL2_coeFn (epsilon : ℝ)
    (hX : MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume) :
    nativeOriginalDampedPrimeFieldL2 epsilon hX =ᵐ[volume] nativeOriginalDampedPrimeField epsilon :=
  hX.coeFn_toLp

theorem nativeOriginalDampedPrimeFieldL2_causal (epsilon : ℝ)
    (hX : MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume) :
    nativeOriginalDampedPrimeFieldL2 epsilon hX ∈ nativeCompletionCausalL2 := by
  filter_upwards [nativeOriginalDampedPrimeFieldL2_coeFn epsilon hX] with t ht
  intro hneg
  rw [ht, nativeOriginalDampedPrimeField_zero_of_neg epsilon hneg]

def nativeOriginalDampedPrimeFieldCausalL2 (epsilon : ℝ)
    (hX : MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume) : nativeCompletionCausalL2 :=
  ⟨nativeOriginalDampedPrimeFieldL2 epsilon hX, nativeOriginalDampedPrimeFieldL2_causal epsilon hX⟩

private theorem pointwise_congr_ae (epsilon : ℝ) {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g)
    (x : ℝ) : nativeDampedCompletionPointwise epsilon f x =
      nativeDampedCompletionPointwise epsilon g x := by
  apply integral_congr_ae
  filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hfg] with s hs
  rw [hs]

/-- A-X supplies only the input class. Its actual operator equation is
derived from the independently proved literal convolution equation. -/
theorem nativeCompletedInput_operator_eq_of_prime_memLp
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hX : MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume) :
    nativeDampedCompletionCausalL2Operator epsilon hepsilon
        (nativeOriginalDampedPrimeFieldCausalL2 epsilon hX) =
      nativeCompletedInputCausalL2 epsilon hepsilon := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [nativeDampedCompletionL2Operator_coeFn_pointwise epsilon hepsilon
      (nativeOriginalDampedPrimeFieldL2 epsilon hX),
    nativeCompletedInputCausalL2_coeFn epsilon hepsilon] with t ht hYt
  exact ht.trans ((pointwise_congr_ae epsilon
    (nativeOriginalDampedPrimeFieldL2_coeFn epsilon hX) t).trans
      ((nativeDampedCompletedInput_equation epsilon t).trans hYt.symm))

theorem nativeCompletedInput_mem_range_of_prime_memLp
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hX : MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume) :
    nativeCompletedInputCausalL2 epsilon hepsilon ∈
      Set.range (nativeDampedCompletionCausalL2Operator epsilon hepsilon) :=
  ⟨nativeOriginalDampedPrimeFieldCausalL2 epsilon hX,
    nativeCompletedInput_operator_eq_of_prime_memLp epsilon hepsilon hX⟩

theorem nativeCompletedInput_mem_rangeClosure_of_prime_memLp
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hX : MemLp (nativeOriginalDampedPrimeField epsilon) 2 volume) :
    nativeCompletedInputCausalL2 epsilon hepsilon ∈
      closure (Set.range (nativeDampedCompletionCausalL2Operator epsilon hepsilon)) :=
  subset_closure (nativeCompletedInput_mem_range_of_prime_memLp epsilon hepsilon hX)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDampedCompletedInput_equation
#print axioms Zeta23.CCM.nativeOriginalDampedPrimeFieldL2_coeFn
#print axioms Zeta23.CCM.nativeCompletedInput_operator_eq_of_prime_memLp
#print axioms Zeta23.CCM.nativeCompletedInput_mem_range_of_prime_memLp
#print axioms Zeta23.CCM.nativeCompletedInput_mem_rangeClosure_of_prime_memLp
