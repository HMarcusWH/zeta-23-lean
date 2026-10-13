import Zeta23.CCM.UniversalSincProductMoments
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Quantitative derivative bounds for the actual inverse integral

The Fourier differentiation theorem consumes the already established actual
product moments. Rescaling by `1/(2π)` cancels the Fourier derivative factors
`(2π)^m`, leaving a uniform Gevrey-order-two bound for `inverseCandidate`.
No derivative estimate is assumed as an input.
-/

noncomputable section

open MeasureTheory
open scoped Topology FourierTransform

namespace Zeta23.CCM.UniversalSinc

private theorem derivative_complex_norm_instances_eq :
    Complex.instNormedAddCommGroup.toNorm = Complex.instNorm := by
  rfl

/-- The scalar moments required by the iterated Fourier derivative theorem
follow from the actual norm moments and continuity. -/
theorem integrable_product_ofReal_smul_moment {s : ℝ} (hs : 0 < s) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m • product s (x : ℂ)) := by
  have hm := integrable_product_ofReal_norm_moment hs m
  rw [← derivative_complex_norm_instances_eq] at hm
  have hn : Integrable (fun x : ℝ => ‖x ^ m • product s (x : ℂ)‖) := by
    simpa only [norm_smul, norm_pow, Real.norm_eq_abs] using hm
  exact (integrable_norm_iff
    ((continuous_id.pow m).smul (continuous_product_ofReal hs.le)).aestronglyMeasurable).mp hn

/-- The exact Fourier differentiation identity for the prescribed product. -/
theorem iteratedDeriv_fourier_product {s : ℝ} (hs : 0 < s) (m : ℕ) :
    iteratedDeriv m (𝓕 (fun x : ℝ => product s (x : ℂ))) =
      𝓕 (fun x : ℝ =>
        (-2 * Real.pi * Complex.I * (x : ℂ)) ^ m • product s (x : ℂ)) := by
  exact Real.iteratedDeriv_fourier (N := ⊤)
    (fun n _ => integrable_product_ofReal_smul_moment hs n) le_top

/-- A uniform Fourier derivative bound expressed in the actual product moment. -/
theorem norm_iteratedDeriv_fourier_product_le_moment
    {s : ℝ} (hs : 0 < s) (m : ℕ) (y : ℝ) :
    ‖iteratedDeriv m (𝓕 (fun x : ℝ => product s (x : ℂ))) y‖ ≤
      (2 * Real.pi) ^ m * ∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖ := by
  rw [iteratedDeriv_fourier_product hs m]
  have hnorm (x : ℝ) :
      ‖(-2 * Real.pi * Complex.I * (x : ℂ)) ^ m • product s (x : ℂ)‖ =
        (2 * Real.pi) ^ m * (|x| ^ m * ‖product s (x : ℂ)‖) := by
    simp only [norm_smul, norm_pow, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      abs_of_pos Real.pi_pos, mul_one]
    norm_num <;> simp only [mul_pow] <;> ring
  calc
    _ ≤ ∫ x : ℝ,
        ‖(-2 * Real.pi * Complex.I * (x : ℂ)) ^ m • product s (x : ℂ)‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) _ y
    _ = _ := by simp_rw [hnorm]; exact integral_const_mul _ _

/-- The paper normalization cancels every Fourier derivative scaling factor. -/
theorem norm_iteratedDeriv_inverseCandidate_le_moment
    {s : ℝ} (hs : 0 < s) (m : ℕ) (y : ℝ) :
    ‖iteratedDeriv m (inverseCandidate s) y‖ ≤
      (1 / (2 * Real.pi)) * ∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖ := by
  let c : ℝ := 1 / (2 * Real.pi)
  have hc : 0 < c := div_pos (by norm_num) (mul_pos (by norm_num) Real.pi_pos)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (fun x : ℝ => product s (x : ℂ))) := by
    apply Real.contDiff_fourier
    intro n _
    have hm := integrable_product_ofReal_norm_moment hs n
    rw [← derivative_complex_norm_instances_eq] at hm
    simpa only [Real.norm_eq_abs] using hm
  have heq : inverseCandidate s = fun x : ℝ =>
      (c : ℂ) * (𝓕 (fun t : ℝ => product s (t : ℂ))) (c * x) := by
    funext x
    rw [inverseCandidate_eq_fourier]
    dsimp only [c]
    congr 2
    ring
  have hd : ‖iteratedDeriv m (inverseCandidate s) y‖ =
      c ^ (m + 1) *
        ‖iteratedDeriv m (𝓕 (fun x : ℝ => product s (x : ℂ))) (c * y)‖ := by
    rw [heq, iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_const_smul (hF.of_le (show (m : ℕ∞) ≤ ⊤ from le_top)) c]
    simp only [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, abs_of_nonneg (pow_nonneg hc.le m)]
    rw [pow_succ]
    ring
  have hcancel : c * (2 * Real.pi) = 1 := by
    dsimp only [c]
    exact div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  have hcancel_pow : c ^ m * (2 * Real.pi) ^ m = 1 := by
    rw [← mul_pow, hcancel, one_pow]
  calc
    _ = c ^ (m + 1) *
        ‖iteratedDeriv m (𝓕 (fun x : ℝ => product s (x : ℂ))) (c * y)‖ := hd
    _ ≤ c ^ (m + 1) * ((2 * Real.pi) ^ m *
        ∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedDeriv_fourier_product_le_moment hs m (c * y))
        (pow_nonneg hc.le _)
    _ = c * ∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖ := by
      rw [pow_succ]
      calc
        _ = c * ((c ^ m * (2 * Real.pi) ^ m) *
            ∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖) := by ring
        _ = _ := by rw [hcancel_pow, one_mul]
    _ = _ := rfl

/-- Explicit Gevrey-order-two constants for the actual inverse integral,
uniform over every real evaluation point. -/
theorem norm_iteratedDeriv_inverseCandidate_le_gevrey
    {s : ℝ} (hs : 0 < s) (m : ℕ) (y : ℝ) :
    ‖iteratedDeriv m (inverseCandidate s) y‖ ≤
      (4 / (Real.pi * (gevreyMomentScale s) ^ 2)) *
        (12 / (gevreyMomentScale s) ^ 2) ^ m * (Nat.factorial m : ℝ) ^ 2 := by
  have hc : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  have hb := gevreyMomentScale_pos hs
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        ∫ x : ℝ, |x| ^ m * ‖product s (x : ℂ)‖ :=
      norm_iteratedDeriv_inverseCandidate_le_moment hs m y
    _ ≤ (1 / (2 * Real.pi)) *
        ((8 / (gevreyMomentScale s) ^ 2) *
          (12 / (gevreyMomentScale s) ^ 2) ^ m * (Nat.factorial m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (product_norm_moment_integral_le_gevrey hs m) hc
    _ = _ := by
      field_simp [Real.pi_ne_zero, hb.ne'] <;> ring

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.integrable_product_ofReal_smul_moment
#print axioms Zeta23.CCM.UniversalSinc.iteratedDeriv_fourier_product
#print axioms Zeta23.CCM.UniversalSinc.norm_iteratedDeriv_fourier_product_le_moment
#print axioms Zeta23.CCM.UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_moment
#print axioms Zeta23.CCM.UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_gevrey
