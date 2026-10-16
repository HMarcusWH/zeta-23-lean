import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Exact discrepancy for the unchanged integer counting measure

With a zero upper boundary, Abel summation and integration by parts identify
the integer-sum-minus-continuum-integral with a bounded floor discrepancy.
The bound is the integral of the actual derivative. No arithmetic cancellation
or a caller-supplied error estimate is assumed. Applying this to the actual
logarithmic drive still requires its smooth extension and change of variables.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Zeta23.CCM

theorem nativeIntegerAbel_discrepancy_eq {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hf : ContDiff ℝ 1 f) (hfb : f b = 0) :
    (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, f k) - (∫ x : ℝ in Set.Ioc 0 b, f x) =
      ∫ x : ℝ in Set.Ioc 0 b, deriv f x * (x - ((⌊x⌋₊ : ℝ) + 1)) := by
  have hD := hf.continuous_deriv le_rfl
  have hDint : IntegrableOn (deriv f) (Set.Icc 0 b) :=
    hD.continuousOn.integrableOn_Icc
  have hsum := sum_mul_eq_sub_integral_mul (fun _ : ℕ => (1 : ℝ)) hb
    (fun x _ => hf.differentiable (by norm_num) x) hDint
  have hcount (x : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, (1 : ℝ)) =
      (⌊x⌋₊ : ℝ) + 1 := by simp
  simp_rw [mul_one, hcount] at hsum
  rw [hfb, zero_mul, zero_sub] at hsum
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := b)
    (u := fun x : ℝ => x) (u' := fun _ => (1 : ℝ))
    (v := f) (v' := deriv f)
    (fun x _ => hasDerivAt_id x)
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt)
    (intervalIntegrable_const) (hD.intervalIntegrable 0 b)
  simp only [hfb, mul_zero, zero_mul, sub_zero, zero_sub, one_mul] at hparts
  rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb] at hparts
  have hxint : IntegrableOn (fun x : ℝ => deriv f x * x) (Set.Ioc 0 b) :=
    ((hD.mul continuous_id).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hcint : IntegrableOn (fun x : ℝ => deriv f x * ((⌊x⌋₊ : ℝ) + 1)) (Set.Ioc 0 b) := by
    have h := integrableOn_mul_sum_Icc (fun _ : ℕ => (1 : ℝ)) (m := 0) le_rfl hDint
    simp_rw [hcount] at h
    exact h.mono_set Ioc_subset_Icc_self
  rw [hsum]
  have hbody : (fun x : ℝ => deriv f x * (x - ((⌊x⌋₊ : ℝ) + 1))) =
      (fun x : ℝ => deriv f x * x - deriv f x * ((⌊x⌋₊ : ℝ) + 1)) := by
    funext x
    ring
  rw [hbody, integral_sub hxint hcint]
  have hcomm : (fun x : ℝ => x * deriv f x) = fun x => deriv f x * x := by
    funext x
    ring
  rw [hcomm] at hparts
  linarith

theorem nativeIntegerAbel_discrepancy_bound {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hf : ContDiff ℝ 1 f) (hfb : f b = 0) :
    |(∑ k ∈ Finset.Icc 0 ⌊b⌋₊, f k) - (∫ x : ℝ in Set.Ioc 0 b, f x)| ≤
      ∫ x : ℝ in Set.Ioc 0 b, |deriv f x| := by
  rw [nativeIntegerAbel_discrepancy_eq hb hf hfb, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le
    (((hf.continuous_deriv le_rfl).abs.continuousOn.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_mul]
  have hx0 : 0 ≤ x := hx.1.le
  have hfloor := Nat.floor_le hx0
  have hupper := Nat.lt_floor_add_one x
  have hdisc : |x - ((⌊x⌋₊ : ℝ) + 1)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  exact (mul_le_mul_of_nonneg_left hdisc (abs_nonneg _)).trans_eq (mul_one _)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeIntegerAbel_discrepancy_eq
#print axioms Zeta23.CCM.nativeIntegerAbel_discrepancy_bound
