import Zeta23.CCM.NativeCausalExponentialWitness
import Zeta23.CCM.NativeAdjointResidual

/-!
# Literal Laplace moments are the actual causal Hilbert pairings

All polynomial degrees and the complex conjugation convention are explicit.
These are moment identities, not an assumed identification with analytic
derivatives or zeta jets. The actual Yepsilon pairing uses its already
proved independent L2 membership and its unchanged c * U representative.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

theorem nativeExponentialPolynomialProfile_conj (w : ℂ) (k : ℕ) (t : ℝ) :
    conj (nativeExponentialPolynomialProfile w k t) =
      (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) := by
  simp only [nativeExponentialPolynomialProfile, map_mul, map_pow,
    Complex.conj_ofReal, ← Complex.exp_conj, map_neg, starRingEnd_self_apply]

def nativeCausalLaplaceMoment (w : ℂ) (k : ℕ) (f : NativeCompletionL2) : ℂ :=
  ∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) * f t

private theorem witness_inner_integrand_ae (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (f : nativeCompletionCausalL2) :
    (fun t : ℝ => inner ℂ (nativeCausalExponentialPolynomialL2 w hw k t)
      ((f : NativeCompletionL2) t)) =ᵐ[volume]
      fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) *
        (f : NativeCompletionL2) t := by
  filter_upwards [nativeCausalExponentialPolynomialL2_coeFn w hw k, f.property] with t ht hft
  rw [ht, RCLike.inner_apply']
  by_cases htpos : 0 ≤ t
  · rw [nativeCausalExponentialPolynomial_of_nonneg w k htpos,
      nativeExponentialPolynomialProfile_conj]
  · rw [hft (lt_of_not_ge htpos), mul_zero, mul_zero]

theorem nativeCausalLaplaceMoment_integrable (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (f : nativeCompletionCausalL2) :
    Integrable (fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) *
      (f : NativeCompletionL2) t) :=
  (L2.integrable_inner (𝕜 := ℂ) (nativeCausalExponentialPolynomialL2 w hw k)
    (f : NativeCompletionL2)).congr (witness_inner_integrand_ae w hw k f)

theorem nativeCausalExponentialWitness_inner_eq_laplaceMoment
    (w : ℂ) (hw : 0 < w.re) (k : ℕ) (f : nativeCompletionCausalL2) :
    inner ℂ (nativeCausalExponentialWitness w hw k) f =
      nativeCausalLaplaceMoment w k (f : NativeCompletionL2) := by
  change inner ℂ (nativeCausalExponentialPolynomialL2 w hw k) (f : NativeCompletionL2) = _
  rw [L2.inner_def]
  exact integral_congr_ae (witness_inner_integrand_ae w hw k f)

/-- The actual stable input's moment has the exact w+epsilon damping shift.
No independent Laplace-transform value or source-jet premise is supplied. -/
theorem nativeCausalExponentialWitness_inner_completedInput
    (w : ℂ) (hw : 0 < w.re) (k : ℕ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    inner ℂ (nativeCausalExponentialWitness w hw k)
        (nativeCompletedInputCausalL2 epsilon hepsilon) =
      ∫ t : ℝ, (t : ℂ) ^ k * Complex.exp (-(w + (epsilon : ℂ)) * (t : ℂ)) *
        (nativeCompletedInput t : ℂ) := by
  rw [nativeCausalExponentialWitness_inner_eq_laplaceMoment, nativeCausalLaplaceMoment]
  apply integral_congr_ae
  filter_upwards [nativeCompletedInputCausalL2_coeFn epsilon hepsilon] with t ht
  rw [ht, nativeDampedCompletedInput, Complex.ofReal_mul, Complex.ofReal_exp]
  rw [Complex.ofReal_mul, Complex.ofReal_neg]
  have he : Complex.exp (-w * (t : ℂ)) * Complex.exp (-(epsilon : ℂ) * (t : ℂ)) =
      Complex.exp (-(w + (epsilon : ℂ)) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (t : ℂ) ^ k * (Complex.exp (-w * (t : ℂ)) *
        Complex.exp (-(epsilon : ℂ) * (t : ℂ))) * (nativeCompletedInput t : ℂ) := by ring
    _ = _ := by rw [he]

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCausalLaplaceMoment_integrable
#print axioms Zeta23.CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment
#print axioms Zeta23.CCM.nativeCausalExponentialWitness_inner_completedInput
