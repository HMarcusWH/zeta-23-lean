import Zeta23.CCM.NativeDampedCompletionOperator
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Actual causal exponential-polynomial L2 test vectors

For Re w > 0, the literal function t^k exp(-conj(w)t), extended by zero
to negative times, defines a nonzero vector in the already constructed
causal complex L2 space. All degrees are retained; no simple-zero
assumption or operator-annihilation premise enters this construction.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ComplexConjugate

namespace Zeta23.CCM

def nativeExponentialPolynomialProfile (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ k * Complex.exp (-conj w * (t : ℂ))

theorem nativeExponentialPolynomialProfile_continuous (w : ℂ) (k : ℕ) :
    Continuous (nativeExponentialPolynomialProfile w k) := by
  unfold nativeExponentialPolynomialProfile
  fun_prop

def nativeCausalExponentialPolynomial (w : ℂ) (k : ℕ) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator (nativeExponentialPolynomialProfile w k)

theorem nativeCausalExponentialPolynomial_of_nonneg (w : ℂ) (k : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    nativeCausalExponentialPolynomial w k t = nativeExponentialPolynomialProfile w k t :=
  indicator_of_mem ht _

theorem nativeCausalExponentialPolynomial_zero_of_neg (w : ℂ) (k : ℕ) {t : ℝ}
    (ht : t < 0) : nativeCausalExponentialPolynomial w k t = 0 :=
  indicator_of_notMem (not_le.mpr ht) _

theorem nativeCausalExponentialPolynomial_measurable (w : ℂ) (k : ℕ) :
    Measurable (nativeCausalExponentialPolynomial w k) :=
  (nativeExponentialPolynomialProfile_continuous w k).measurable.indicator measurableSet_Ici

theorem nativeCausalExponentialPolynomial_norm (w : ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖nativeCausalExponentialPolynomial w k t‖ = t ^ k * Real.exp (-w.re * t) := by
  rw [nativeCausalExponentialPolynomial_of_nonneg w k ht,
    nativeExponentialPolynomialProfile, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg ht, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem nativeCausalExponentialPolynomial_norm_sq (w : ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖nativeCausalExponentialPolynomial w k t‖ ^ 2 =
      t ^ (2 * k) * Real.exp (-(2 * w.re) * t) := by
  rw [nativeCausalExponentialPolynomial_norm w k ht, mul_pow]
  have hpow : (t ^ k) ^ 2 = t ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm]
  rw [hpow, pow_two, ← Real.exp_add]
  congr 2
  ring

private theorem positive_pow_exp_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-a * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := (1 : ℝ)) (b := a)
    (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) ha
  simpa only [Real.rpow_natCast, Real.rpow_one] using! h

theorem nativeCausalExponentialPolynomial_norm_sq_integrable {w : ℂ}
    (hw : 0 < w.re) (k : ℕ) :
    Integrable (fun t : ℝ => ‖nativeCausalExponentialPolynomial w k t‖ ^ 2) := by
  have hpos : IntegrableOn
      (fun t : ℝ => ‖nativeCausalExponentialPolynomial w k t‖ ^ 2) (Ioi 0) :=
    (positive_pow_exp_integrable (2 * k) (mul_pos (by norm_num) hw)).congr_fun
      (fun t ht => (nativeCausalExponentialPolynomial_norm_sq w k
        (show (0 : ℝ) < t from ht).le).symm) measurableSet_Ioi
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0)).congr_fun
    (fun t ht => by
      change (0 : ℝ) = ‖nativeCausalExponentialPolynomial w k t‖ ^ 2
      rw [nativeCausalExponentialPolynomial_zero_of_neg w k ht, norm_zero]
      norm_num) measurableSet_Iio

theorem nativeCausalExponentialPolynomial_memLp {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    MemLp (nativeCausalExponentialPolynomial w k) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (nativeCausalExponentialPolynomial_measurable w k).aestronglyMeasurable).mpr
      (nativeCausalExponentialPolynomial_norm_sq_integrable hw k)

def nativeCausalExponentialPolynomialL2 (w : ℂ) (hw : 0 < w.re) (k : ℕ) : NativeCompletionL2 :=
  (nativeCausalExponentialPolynomial_memLp hw k).toLp (nativeCausalExponentialPolynomial w k)

theorem nativeCausalExponentialPolynomialL2_coeFn (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    nativeCausalExponentialPolynomialL2 w hw k =ᵐ[volume] nativeCausalExponentialPolynomial w k :=
  (nativeCausalExponentialPolynomial_memLp hw k).coeFn_toLp

theorem nativeCausalExponentialPolynomialL2_causal (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    nativeCausalExponentialPolynomialL2 w hw k ∈ nativeCompletionCausalL2 := by
  change ∀ᵐ t : ℝ, t < 0 → nativeCausalExponentialPolynomialL2 w hw k t = 0
  filter_upwards [nativeCausalExponentialPolynomialL2_coeFn w hw k] with t ht
  intro htneg
  rw [ht]
  exact nativeCausalExponentialPolynomial_zero_of_neg w k htneg

theorem nativeCausalExponentialPolynomialL2_ne_zero (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    nativeCausalExponentialPolynomialL2 w hw k ≠ 0 := by
  intro hzero
  have hz : nativeCausalExponentialPolynomial w k =ᵐ[volume] (fun _ => (0 : ℂ)) := by
    have hrep := nativeCausalExponentialPolynomialL2_coeFn w hw k
    rw [hzero] at hrep
    exact hrep.symm.trans (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ))
  have hp : nativeExponentialPolynomialProfile w k =ᵐ[volume.restrict (Ioi 0)]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hz] with t ht htz
    rw [nativeCausalExponentialPolynomial_of_nonneg w k (show (0 : ℝ) < t from ht).le] at htz
    exact htz
  have hpoint := Measure.eqOn_open_of_ae_eq hp isOpen_Ioi
    (nativeExponentialPolynomialProfile_continuous w k).continuousOn continuous_const.continuousOn
  have h1 := hpoint (show (1 : ℝ) ∈ Ioi 0 by norm_num)
  have hne : nativeExponentialPolynomialProfile w k 1 ≠ 0 := by
    simp only [nativeExponentialPolynomialProfile, Complex.ofReal_one, one_pow, one_mul, mul_one]
    exact Complex.exp_ne_zero _
  exact hne h1

def nativeCausalExponentialWitness (w : ℂ) (hw : 0 < w.re) (k : ℕ) : nativeCompletionCausalL2 :=
  ⟨nativeCausalExponentialPolynomialL2 w hw k, nativeCausalExponentialPolynomialL2_causal w hw k⟩

theorem nativeCausalExponentialWitness_ne_zero (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    nativeCausalExponentialWitness w hw k ≠ 0 := by
  intro hz
  exact nativeCausalExponentialPolynomialL2_ne_zero w hw k (congrArg Subtype.val hz)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCausalExponentialPolynomial_norm_sq_integrable
#print axioms Zeta23.CCM.nativeCausalExponentialPolynomial_memLp
#print axioms Zeta23.CCM.nativeCausalExponentialPolynomialL2_coeFn
#print axioms Zeta23.CCM.nativeCausalExponentialPolynomialL2_causal
#print axioms Zeta23.CCM.nativeCausalExponentialWitness_ne_zero
