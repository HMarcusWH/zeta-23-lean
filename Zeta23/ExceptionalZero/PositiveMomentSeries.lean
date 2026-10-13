import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Positive moment series and exponential integrability

For an almost everywhere nonnegative real variable, Tonelli identifies the
extended integral of its exponential with the series of integrated Taylor
terms. Thus summability of that positive moment series implies genuine
exponential integrability. The measure need not be a probability measure.

This is a general analytic prerequisite. No summability premise for an
actual zeta correlation or its positive tail is discharged in this file.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology Nat

namespace Zeta23.ExceptionalZero

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {h : ℝ}

/-- Tonelli's formula for the exponential of a nonnegative variable.
The equality is in `ℝ≥0∞`, so no convergence of the moment series is assumed. -/
theorem lintegral_exp_mul_eq_tsum_positive_moments
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hh : 0 ≤ h)
    (hmoment : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (h * X ω)) ∂μ) =
      ∑' n : ℕ, ENNReal.ofReal
        ((h ^ n / (n ! : ℝ)) * ∫ ω, X ω ^ n ∂μ) := by
  let F : ℕ → Ω → ℝ := fun n ω => (h ^ n / (n ! : ℝ)) * X ω ^ n
  have hFint (n : ℕ) : Integrable (F n) μ :=
    (hmoment n).const_mul (h ^ n / (n ! : ℝ))
  have hFnn (n : ℕ) : ∀ᵐ ω ∂μ, 0 ≤ F n ω := by
    filter_upwards [hX] with ω hω
    exact mul_nonneg (div_nonneg (pow_nonneg hh n) (Nat.cast_nonneg _))
      (pow_nonneg hω n)
  have hpoint (ω : Ω) :
      HasSum (fun n : ℕ => F n ω) (Real.exp (h * X ω)) := by
    simpa only [F, mul_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (h * X ω))
  have hterm (n : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) =
        ENNReal.ofReal ((h ^ n / (n ! : ℝ)) * ∫ ω, X ω ^ n ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint n) (hFnn n)]
    simp only [F, integral_const_mul]
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp (h * X ω)) ∂μ) =
        ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal (F n ω) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hX] with ω hω
      rw [← (hpoint ω).tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg
          (div_nonneg (pow_nonneg hh n) (Nat.cast_nonneg _)) (pow_nonneg hω n))
        (hpoint ω).summable
    _ = ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ :=
      lintegral_tsum (fun n => (hFint n).aemeasurable.ennreal_ofReal)
    _ = _ := tsum_congr hterm

/-- A summable positive integrated Taylor series supplies exponential
integrability. In particular this applies at every strictly positive `h`. -/
theorem integrable_exp_mul_of_summable_positive_moments
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hh : 0 ≤ h)
    (hmoment : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ)
    (hsum : Summable (fun n : ℕ =>
      (h ^ n / (n ! : ℝ)) * ∫ ω, X ω ^ n ∂μ)) :
    Integrable (fun ω => Real.exp (h * X ω)) μ := by
  have hXmeas : AEMeasurable X μ := by
    simpa only [pow_one] using (hmoment 1).aemeasurable
  refine ⟨(hXmeas.const_mul h).exp.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun ω => (Real.exp_pos (h * X ω)).le)).mpr
  rw [lintegral_exp_mul_eq_tsum_positive_moments hX hh hmoment]
  exact hsum.tsum_ofReal_lt_top

/-- The convergent positive moment series also computes the real integral. -/
theorem integral_exp_mul_eq_tsum_positive_moments
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hh : 0 ≤ h)
    (hmoment : ∀ n : ℕ, Integrable (fun ω => X ω ^ n) μ)
    (hsum : Summable (fun n : ℕ =>
      (h ^ n / (n ! : ℝ)) * ∫ ω, X ω ^ n ∂μ)) :
    (∫ ω, Real.exp (h * X ω) ∂μ) =
      ∑' n : ℕ, (h ^ n / (n ! : ℝ)) * ∫ ω, X ω ^ n ∂μ := by
  let F : ℕ → Ω → ℝ := fun n ω => (h ^ n / (n ! : ℝ)) * X ω ^ n
  have hFint (n : ℕ) : Integrable (F n) μ :=
    (hmoment n).const_mul (h ^ n / (n ! : ℝ))
  have hnorm (n : ℕ) :
      (∫ ω, ‖F n ω‖ ∂μ) =
        (h ^ n / (n ! : ℝ)) * ∫ ω, X ω ^ n ∂μ := by
    calc
      (∫ ω, ‖F n ω‖ ∂μ) = ∫ ω, F n ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hX] with ω hω
        exact Real.norm_of_nonneg (mul_nonneg
          (div_nonneg (pow_nonneg hh n) (Nat.cast_nonneg _)) (pow_nonneg hω n))
      _ = _ := by simp only [F, integral_const_mul]
  have hnormsum : Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂μ) :=
    hsum.congr (fun n => (hnorm n).symm)
  have hpoint (ω : Ω) : (∑' n : ℕ, F n ω) = Real.exp (h * X ω) := by
    simpa only [F, mul_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (h * X ω)).tsum_eq
  calc
    (∫ ω, Real.exp (h * X ω) ∂μ) = ∫ ω, ∑' n : ℕ, F n ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (hpoint ω).symm
    _ = ∑' n : ℕ, ∫ ω, F n ω ∂μ :=
      (integral_tsum_of_summable_integral_norm hFint hnormsum).symm
    _ = _ := by simp only [F, integral_const_mul]

#print axioms lintegral_exp_mul_eq_tsum_positive_moments
#print axioms integrable_exp_mul_of_summable_positive_moments
#print axioms integral_exp_mul_eq_tsum_positive_moments

end Zeta23.ExceptionalZero
