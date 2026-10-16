import Zeta23.CCM.NativeCausalLaplaceMoments
import Mathlib.Data.Nat.Choose.Sum

/-!
# Actual causal completion pairings and polynomial zero-jet tests

The kernel moments below integrate the literal damped floor kernel. A
kernel-moment vanishing condition is kept distinct from a proved zeta zero
identity. Every polynomial degree is retained in the finite translation
formula; no simple-root specialization or truncation of multiplicity is
used.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped Topology BigOperators ComplexConjugate

namespace Zeta23.CCM

def nativeCompletionKernelLaplaceMoment (epsilon : ℝ) (w : ℂ) (k : ℕ) : ℂ :=
  ∫ t : ℝ, (nativeDampedCompletionKernel epsilon t : ℂ) *
    (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ))

private theorem laplace_pow_exp_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-a * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := (1 : ℝ)) (b := a)
    (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) ha
  simpa only [Real.rpow_natCast, Real.rpow_one] using! h

theorem nativeCompletionKernelLaplaceMoment_integrable (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    Integrable (fun t : ℝ => (nativeDampedCompletionKernel epsilon t : ℂ) *
      (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ))) := by
  have hpos : IntegrableOn (fun t : ℝ => (nativeDampedCompletionKernel epsilon t : ℂ) *
      (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ))) (Ioi 0) := by
    apply (laplace_pow_exp_integrable k (show 0 < w.re + 1 / 2 by linarith)).mono'
    · exact ((nativeDampedCompletionKernel_measurable epsilon).complex_ofReal.mul
        (Complex.measurable_ofReal.pow_const k)).mul
          (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
          |>.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0 : ℝ) < t := ht
    rw [norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (nativeDampedCompletionKernel_nonneg epsilon t), norm_pow,
      Complex.norm_real, Real.norm_of_nonneg htpos.le, Complex.norm_exp]
    have hre : (-w * (t : ℂ)).re = -w.re * t := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
    rw [hre]
    have hkernel := (nativeDampedCompletionKernel_le_native hepsilon t).trans
      (nativePositiveCompletion_le_exp t)
    calc
      _ ≤ Real.exp (-(t / 2)) * t ^ k * Real.exp (-w.re * t) := by
        gcongr
      _ = _ := by
        calc
          _ = t ^ k * (Real.exp (-(t / 2)) * Real.exp (-w.re * t)) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Iio 0)).congr_fun
    (fun t ht => by
      change (0 : ℂ) = (nativeDampedCompletionKernel epsilon t : ℂ) *
        (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ))
      rw [nativeDampedCompletionKernel_zero_of_neg epsilon ht, Complex.ofReal_zero, zero_mul,
        zero_mul]) measurableSet_Iio

/-- Every finite delay has the exact binomial action on all polynomial
Laplace moments. The source function is only assumed causal L2. -/
theorem nativeCausalLaplaceMoment_delay (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (f : nativeCompletionCausalL2) (s : ℝ) :
    nativeCausalLaplaceMoment w k (nativeCompletionL2Delay s (f : NativeCompletionL2)) =
      Complex.exp (-w * (s : ℂ)) * ∑ j ∈ range (k + 1),
        (k.choose j : ℂ) * (s : ℂ) ^ (k - j) *
          nativeCausalLaplaceMoment w j (f : NativeCompletionL2) := by
  unfold nativeCausalLaplaceMoment
  have hrep : (fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) *
      nativeCompletionL2Delay s (f : NativeCompletionL2) t) =ᵐ[volume]
      fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) *
        (f : NativeCompletionL2) (t - s) := by
    filter_upwards [nativeCompletionL2Delay_coeFn s (f : NativeCompletionL2)] with t ht
    rw [ht]
  rw [integral_congr_ae hrep]
  let F : ℝ → ℂ := fun u => ((u + s : ℝ) : ℂ) ^ k *
    Complex.exp (-w * ((u + s : ℝ) : ℂ)) * (f : NativeCompletionL2) u
  have hshift : (fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-w * (t : ℂ)) *
      (f : NativeCompletionL2) (t - s)) = fun t => F (t - s) := by
    funext t
    simp only [F, sub_add_cancel]
  rw [hshift, integral_sub_right_eq_self]
  have hpoint (u : ℝ) : F u = ∑ j ∈ range (k + 1),
      (Complex.exp (-w * (s : ℂ)) * ((k.choose j : ℂ) * (s : ℂ) ^ (k - j))) *
        ((u : ℂ) ^ j * Complex.exp (-w * (u : ℂ)) * (f : NativeCompletionL2) u) := by
    have he : Complex.exp (-w * ((u + s : ℝ) : ℂ)) =
        Complex.exp (-w * (u : ℂ)) * Complex.exp (-w * (s : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp only [F]
    rw [he, Complex.ofReal_add, add_pow]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_finsetSum]
  · simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j _
    exact (nativeCausalLaplaceMoment_integrable w hw j f).const_mul _

/-- The exact finite moment formula for the actual bounded causal operator.
This is obtained from its strong integral and the proved finite delay
formula, rather than assuming a pointwise L2 convolution representative. -/
theorem nativeCausalExponentialWitness_inner_operator
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (f : nativeCompletionCausalL2) :
    inner ℂ (nativeCausalExponentialWitness w hw k)
        (nativeDampedCompletionCausalL2Operator epsilon hepsilon f) =
      ∑ j ∈ range (k + 1), (k.choose j : ℂ) *
        nativeCausalLaplaceMoment w j (f : NativeCompletionL2) *
          nativeCompletionKernelLaplaceMoment epsilon w (k - j) := by
  have hi : inner ℂ (nativeCausalExponentialWitness w hw k)
        (nativeDampedCompletionCausalL2Operator epsilon hepsilon f) =
      ∫ s : ℝ, inner ℂ (nativeCausalExponentialPolynomialL2 w hw k)
        (nativeDampedCompletionL2Integrand epsilon (f : NativeCompletionL2) s) := by
    change inner ℂ (nativeCausalExponentialPolynomialL2 w hw k)
      (nativeDampedCompletionL2Operator epsilon hepsilon (f : NativeCompletionL2)) = _
    rw [nativeDampedCompletionL2Operator_apply]
    change inner ℂ (nativeCausalExponentialPolynomialL2 w hw k)
      (∫ s : ℝ, nativeDampedCompletionL2Integrand epsilon (f : NativeCompletionL2) s) = _
    exact (integral_inner (𝕜 := ℂ)
      (nativeDampedCompletionL2Integrand_integrable hepsilon (f : NativeCompletionL2))
      (nativeCausalExponentialPolynomialL2 w hw k)).symm
  rw [hi]
  have hpoint (s : ℝ) : inner ℂ (nativeCausalExponentialPolynomialL2 w hw k)
      (nativeDampedCompletionL2Integrand epsilon (f : NativeCompletionL2) s) =
      ∑ j ∈ range (k + 1),
        ((k.choose j : ℂ) * nativeCausalLaplaceMoment w j (f : NativeCompletionL2)) *
          ((nativeDampedCompletionKernel epsilon s : ℂ) * (s : ℂ) ^ (k - j) *
            Complex.exp (-w * (s : ℂ))) := by
    by_cases hs : 0 ≤ s
    · let delayed : nativeCompletionCausalL2 :=
        ⟨nativeCompletionL2Delay s (f : NativeCompletionL2),
          nativeCompletionL2Delay_causal hs (f : NativeCompletionL2) f.property⟩
      have hd := nativeCausalExponentialWitness_inner_eq_laplaceMoment w hw k delayed
      change inner ℂ (nativeCausalExponentialPolynomialL2 w hw k)
          (nativeCompletionL2Delay s (f : NativeCompletionL2)) =
        nativeCausalLaplaceMoment w k (nativeCompletionL2Delay s (f : NativeCompletionL2)) at hd
      rw [nativeDampedCompletionL2Integrand, RCLike.real_smul_eq_coe_smul (K := ℂ),
        inner_smul_right, hd, nativeCausalLaplaceMoment_delay w hw k f s,
        Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [RCLike.ofReal_eq_complex_ofReal]
      ring
    · rw [nativeDampedCompletionL2Integrand,
        nativeDampedCompletionKernel_zero_of_neg epsilon (lt_of_not_ge hs), zero_smul,
        inner_zero_right]
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, sum_const_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_finsetSum]
  · simp_rw [integral_const_mul]
    rfl
  · intro j _
    exact (nativeCompletionKernelLaplaceMoment_integrable epsilon hepsilon w hw (k - j)).const_mul _

/-- Vanishing of all actual kernel moments through degree k annihilates
the actual range. This is a conditional moment criterion; obtaining these
moments from a zeta zero is a separate theorem. -/
theorem nativeCausalExponentialWitness_annihilates_range_of_kernel_moments
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (hzero : ∀ j ≤ k, nativeCompletionKernelLaplaceMoment epsilon w j = 0)
    (f : nativeCompletionCausalL2) :
    inner ℂ (nativeCausalExponentialWitness w hw k)
      (nativeDampedCompletionCausalL2Operator epsilon hepsilon f) = 0 := by
  rw [nativeCausalExponentialWitness_inner_operator]
  apply Finset.sum_eq_zero
  intro j _
  rw [hzero (k - j) (Nat.sub_le _ _), mul_zero]

/-- The preceding range annihilator belongs to the kernel of the true
causal Hilbert adjoint, rather than the full-line adjoint. -/
theorem nativeCausalExponentialWitness_mem_adjointKernel_of_kernel_moments
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (hzero : ∀ j ≤ k, nativeCompletionKernelLaplaceMoment epsilon w j = 0) :
    nativeDampedCompletionCausalL2Adjoint epsilon hepsilon
      (nativeCausalExponentialWitness w hw k) = 0 := by
  apply ext_inner_right ℂ
  intro f
  rw [inner_zero_left]
  exact (nativeDampedCompletionCausalL2Operator epsilon hepsilon).adjoint_inner_left f
    (nativeCausalExponentialWitness w hw k) |>.trans
      (nativeCausalExponentialWitness_annihilates_range_of_kernel_moments
        epsilon hepsilon w hw k hzero f)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCompletionKernelLaplaceMoment_integrable
#print axioms Zeta23.CCM.nativeCausalLaplaceMoment_delay
#print axioms Zeta23.CCM.nativeCausalExponentialWitness_inner_operator
#print axioms Zeta23.CCM.nativeCausalExponentialWitness_annihilates_range_of_kernel_moments
#print axioms Zeta23.CCM.nativeCausalExponentialWitness_mem_adjointKernel_of_kernel_moments
