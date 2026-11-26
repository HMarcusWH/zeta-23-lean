import Zeta23.RHReference.Perron.LiteralRampMellin
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.Ring

/-!
Absolute interchange of the von Mangoldt Dirichlet series and the Re s = 2
Perron integral for the exact literal finite prime ramp.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set ArithmeticFunction

namespace Zeta23.RHReference

private def verticalTwo (t : ℝ) : ℂ := ((2 : ℝ) : ℂ) + t * I

private theorem verticalTwo_re (t : ℝ) : (verticalTwo t).re = 2 := by
  simp [verticalTwo]

private theorem continuous_verticalTwo : Continuous verticalTwo :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

def perronLineTwoTerm (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (fun n => (vonMangoldt n : ℂ)) (verticalTwo t) n *
    (perronRampTransform (verticalTwo t) * (x : ℂ) ^ verticalTwo t)

private theorem continuous_verticalTwoRamp :
    Continuous (fun t => perronRampTransform (verticalTwo t)) := by
  unfold perronRampTransform
  apply continuous_const.div
  · exact continuous_verticalTwo.mul (continuous_verticalTwo.sub continuous_const)
  · intro t
    apply mul_ne_zero
    · intro heq
      have hr := congrArg Complex.re heq
      rw [verticalTwo_re, Complex.zero_re] at hr
      norm_num at hr
    · intro heq
      have hr := congrArg Complex.re (sub_eq_zero.mp heq)
      rw [verticalTwo_re, Complex.one_re] at hr
      norm_num at hr

private theorem verticalTwo_cpow_ne_zero {a : ℂ} (ha : a ≠ 0) (t : ℝ) :
    a ^ verticalTwo t ≠ 0 := by
  exact fun h => ha ((Complex.cpow_eq_zero_iff _ _).mp h).1

private theorem perronLineTwoTerm_continuous {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Continuous (perronLineTwoTerm x n) := by
  change Continuous (fun t : ℝ => perronLineTwoTerm x n t)
  by_cases hn : n = 0
  · subst n
    simpa [perronLineTwoTerm] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    simp only [perronLineTwoTerm, LSeries.term_of_ne_zero hn]
    exact (continuous_const.div
      (continuous_verticalTwo.const_cpow (Or.inl hnC)) (verticalTwo_cpow_ne_zero hnC)).mul
      (continuous_verticalTwoRamp.mul (continuous_verticalTwo.const_cpow (Or.inl hxC)))

private def perronLineTwoMajorant (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (‖LSeries.term (fun n => (vonMangoldt n : ℂ)) 2 n‖ * x ^ 2) * (1 + t ^ 2)⁻¹

theorem norm_perronLineTwoTerm_le {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖perronLineTwoTerm x n t‖ ≤
      (‖LSeries.term (fun n => (vonMangoldt n : ℂ)) 2 n‖ * x ^ 2) * (1 + t ^ 2)⁻¹ := by
  have hn : ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) (verticalTwo t) n‖ =
     ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) 2 n‖ := by
    simp only [LSeries.norm_term_eq, verticalTwo_re]
    norm_num
  have hxpow : ‖(x : ℂ) ^ verticalTwo t‖ = x ^ 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, verticalTwo_re, Real.rpow_two]
  have hW : ‖perronRampTransform (verticalTwo t)‖ ≤ (1 + t ^ 2)⁻¹ := by
    simpa [verticalTwo] using norm_perronRampTransform_vertical_two t
  rw [perronLineTwoTerm, norm_mul, norm_mul, hn, hxpow]
  calc
    _ ≤ ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) 2 n‖ *
        ((1 + t ^ 2)⁻¹ * x ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW (sq_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private theorem perronLineTwoMajorant_integrable (x : ℝ) (n : ℕ) :
    Integrable (perronLineTwoMajorant x n) :=
  integrable_inv_one_add_sq.const_mul _

theorem perronLineTwoTerm_integrable {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Integrable (perronLineTwoTerm x n) :=
  (perronLineTwoMajorant_integrable x n).mono' (perronLineTwoTerm_continuous hx n).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_perronLineTwoTerm_le hx n))

theorem perronLineTwo_summable_integral_norm {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖perronLineTwoTerm x n t‖) := by
  have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ))
    (by norm_num)).norm
  have hMajorant : Summable (fun n : ℕ => ∫ t : ℝ, perronLineTwoMajorant x n t) := by
    simpa only [perronLineTwoMajorant, integral_const_mul] using
      (hL.mul_right (x ^ 2)).mul_right (∫ t : ℝ, (1 + t ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => integral_mono (perronLineTwoTerm_integrable hx n).norm
      (perronLineTwoMajorant_integrable x n) (norm_perronLineTwoTerm_le hx n)) hMajorant

theorem integral_tsum_perronLineTwo {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, ∑' n : ℕ, perronLineTwoTerm x n t) =
      ∑' n : ℕ, ∫ t : ℝ, perronLineTwoTerm x n t :=
  (integral_tsum_of_summable_integral_norm (perronLineTwoTerm_integrable hx)
    (perronLineTwo_summable_integral_norm hx)).symm

private theorem perronLineTwoTerm_ratio {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    perronLineTwoTerm x n t = (vonMangoldt n : ℂ) *
      (((↑((n : ℝ) / x) : ℂ) ^ (-verticalTwo t)) * perronRampTransform (verticalTwo t)) := by
  by_cases hn : n = 0
  · simp [hn, perronLineTwoTerm]
  rw [perronLineTwoTerm, LSeries.term_of_ne_zero hn, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg n) hx.le]
  simp only [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv, inv_inv]
  ring

private theorem complex_normalization (z : ℂ) :
    (1 / (2 * Real.pi : ℝ)) • z = (1 / (2 * (Real.pi : ℂ))) * z := by
  simp [Complex.real_smul]

private theorem perronLineTwo_inverse_term {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, perronLineTwoTerm x n t) =
      (vonMangoldt n : ℂ) * perronRamp ((n : ℝ) / x) := by
  by_cases hn : n = 0
  · simp [hn, perronLineTwoTerm]
  have hy : 0 < (n : ℝ) / x := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hx
  rw [show (fun t => perronLineTwoTerm x n t) = (fun t : ℝ =>
    (vonMangoldt n : ℂ) *
      (((↑((n : ℝ) / x) : ℂ) ^ (-verticalTwo t)) * perronRampTransform (verticalTwo t))) from
        funext (perronLineTwoTerm_ratio hx n), integral_const_mul, ← mul_assoc, mul_comm _ (vonMangoldt n : ℂ),
        mul_assoc]
  congr 1
  simpa only [mellinInv, verticalTwo, smul_eq_mul, complex_normalization] using
    mellinInv_perronRampTransform hy

/-- Right-line inversion with the literal max-weighted von Mangoldt ramp. -/
theorem rightLinePerron_eq_tsum {x : ℝ} (hx : 0 < x) :
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ, (-deriv riemannZeta (verticalTwo t) / riemannZeta (verticalTwo t)) *
        (perronRampTransform (verticalTwo t) * (x : ℂ) ^ verticalTwo t)) =
      ∑' n : ℕ, (vonMangoldt n : ℂ) * perronRamp ((n : ℝ) / x) := by
  have hSeries (t : ℝ) :
      (-deriv riemannZeta (verticalTwo t) / riemannZeta (verticalTwo t)) *
        (perronRampTransform (verticalTwo t) * (x : ℂ) ^ verticalTwo t) =
      ∑' n : ℕ, perronLineTwoTerm x n t := by
    rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by rw [verticalTwo_re]; norm_num)]
    unfold LSeries
    rw [← tsum_mul_right]
    rfl
  simp_rw [hSeries]
  rw [integral_tsum_perronLineTwo hx, ← tsum_mul_left]
  exact tsum_congr (perronLineTwo_inverse_term hx)

/-- Exact finite-native ramp, including any integer endpoint with its zero weight. -/
theorem tsum_perronRamp_eq_native_sum {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (vonMangoldt n : ℂ) * perronRamp ((n : ℝ) / x)) =
      ↑(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n * (x / (n : ℝ) - 1)) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊), Complex.ofReal_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnx : (n : ℝ) ≤ x :=
      (Nat.le_floor_iff hx.le).1 (Finset.mem_Icc.mp hn).2
    unfold perronRamp
    rw [inv_div, max_eq_left (sub_nonneg.mpr ((le_div_iff₀ hnpos).2 (by simpa using hnx)))]
    simp
  · intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnx : x < (n : ℝ) := by
      by_contra! h
      exact hn (Finset.mem_Icc.mpr ⟨hn1, (Nat.le_floor_iff hx.le).2 h⟩)
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    unfold perronRamp
    rw [inv_div, max_eq_right (sub_nonpos.mpr ((div_le_iff₀ hnpos).2 (by simpa using hnx.le)))]
    simp

/-- Line Re s = 2 sees exactly the uncentered finite source of native literalG. -/
theorem rightLinePerron_eq_native_sum {x : ℝ} (hx : 0 < x) :
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ, (-deriv riemannZeta (verticalTwo t) / riemannZeta (verticalTwo t)) *
        (perronRampTransform (verticalTwo t) * (x : ℂ) ^ verticalTwo t)) =
      ↑(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n * (x / (n : ℝ) - 1)) :=
  (rightLinePerron_eq_tsum hx).trans (tsum_perronRamp_eq_native_sum hx)

#print axioms Zeta23.RHReference.integral_tsum_perronLineTwo
#print axioms Zeta23.RHReference.tsum_perronRamp_eq_native_sum
#print axioms Zeta23.RHReference.rightLinePerron_eq_native_sum

end Zeta23.RHReference
