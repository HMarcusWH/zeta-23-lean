import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory
open scoped Interval

/-! # Complex exponential first moment

This helper isolates the first complex exponential moment used by the canonical
dictionary tent transform.  The pinned Mathlib revision exposes multiple
propositionally equivalent real-module proofs on `ℂ`; following Mathlib's own
`integral_exp_mul_complex` implementation, the `comp_ofReal` steps use
`simpa ... using!` so dependent typeclass arguments are reconciled rather than
required to be definitionally identical.
-/

/-- Primitive for the first exponential moment `y * exp(c*y)`. -/
def complexMulExpPrimitive (c : ℂ) (y : ℝ) : ℂ :=
  ((y : ℂ) / c - 1 / c ^ 2) * Complex.exp (c * y)

private theorem hasDerivAt_complexMulExpPrimitive
    {c : ℂ} (hc : c ≠ 0) (y : ℝ) :
    HasDerivAt (complexMulExpPrimitive c)
      ((y : ℂ) * Complex.exp (c * y)) y := by
  have hdiv : HasDerivAt (fun t : ℝ => (t : ℂ) / c) (1 / c) y := by
    simpa only [mul_one] using!
      (((hasDerivAt_id (y : ℂ)).div_const c).comp_ofReal)
  have hleft : HasDerivAt
      (fun t : ℝ => (t : ℂ) / c - 1 / c ^ 2) (1 / c) y :=
    hdiv.sub_const _
  have hlin : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c y := by
    simpa only [mul_one] using!
      (((hasDerivAt_id (y : ℂ)).const_mul c).comp_ofReal)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * t))
      (c * Complex.exp (c * y)) y := by
    simpa [Function.comp_def, mul_comm] using!
      ((Complex.hasDerivAt_exp (c * (y : ℂ))).comp y hlin)
  have hprod : HasDerivAt
      (fun t : ℝ => ((t : ℂ) / c - 1 / c ^ 2) * Complex.exp (c * t))
      ((1 / c) * Complex.exp (c * y) +
        ((y : ℂ) / c - 1 / c ^ 2) * (c * Complex.exp (c * y))) y :=
    hleft.mul hexp
  change HasDerivAt
    (fun t : ℝ => ((t : ℂ) / c - 1 / c ^ 2) * Complex.exp (c * t))
    ((y : ℂ) * Complex.exp (c * y)) y
  convert hprod using 1
  field_simp [hc] <;> ring

/-- Exact first moment of a complex exponential over a real interval. -/
theorem intervalIntegral_mul_exp_complex
    {a b : ℝ} {c : ℂ} (hc : c ≠ 0) :
    (∫ y in a..b, (y : ℂ) * Complex.exp (c * y)) =
      complexMulExpPrimitive c b - complexMulExpPrimitive c a := by
  have hint : IntervalIntegrable
      (fun y : ℝ => (y : ℂ) * Complex.exp (c * y)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := complexMulExpPrimitive c)
    (f' := fun y : ℝ => (y : ℂ) * Complex.exp (c * y))
    (fun y _ => hasDerivAt_complexMulExpPrimitive hc y) hint

end Zeta23.CCM