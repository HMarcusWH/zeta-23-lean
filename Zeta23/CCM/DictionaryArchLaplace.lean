import Zeta23.CCM.DictionaryArchBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set

/-! # Laplace representation of the archimedean digamma summands

This file is downstream of the already-green digamma-series bridge.  It does not
change any existing channel normalization and does not invoke the explicit
formula.  The first gate is the scalar Laplace transform needed to convert one
positive-abscissa rational summand into physical space.
-/

/-- Real Laplace transform of a cosine on the positive half-line. -/
theorem integral_exp_neg_mul_cos_Ioi
    {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ in Ioi 0, Real.exp (-a * x) * Real.cos (t * x)) =
      a / (a ^ 2 + t ^ 2) := by
  let z : ℂ := ((-a : ℝ) : ℂ) + I * (t : ℂ)
  have hz : z.re < 0 := by
    dsimp [z]
    simp [ha]
  have hcomplex := integral_exp_mul_complex_Ioi (a := z) hz 0
  have hint : IntegrableOn (fun x : ℝ => Complex.exp (z * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hz 0
  have hleft :
      (fun x : ℝ => (Complex.exp (z * x)).re) =
        fun x : ℝ => Real.exp (-a * x) * Real.cos (t * x) := by
    funext x
    rw [Complex.exp_re]
    dsimp [z]
    simp [Complex.mul_re, Complex.mul_im]
  have hright : (-Complex.exp (z * (0 : ℝ)) / z).re =
      a / (a ^ 2 + t ^ 2) := by
    dsimp [z]
    simp [Complex.div_re, Complex.normSq_apply]
    ring
  calc
    (∫ x : ℝ in Ioi 0, Real.exp (-a * x) * Real.cos (t * x)) =
        ∫ x : ℝ in Ioi 0, (Complex.exp (z * x)).re := by rw [hleft]
    _ = (∫ x : ℝ in Ioi 0, Complex.exp (z * x)).re := integral_re hint
    _ = (-Complex.exp (z * (0 : ℝ)) / z).re := by rw [hcomplex]
    _ = a / (a ^ 2 + t ^ 2) := hright

/-- Integral form of one positive-abscissa digamma difference term. -/
theorem integral_exp_neg_mul_one_sub_cos_Ioi
    {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ in Ioi 0,
      Real.exp (-a * x) * (1 - Real.cos (t * x))) =
      1 / a - a / (a ^ 2 + t ^ 2) := by
  have hExp : IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
  have hCos : IntegrableOn
      (fun x : ℝ => Real.exp (-a * x) * Real.cos (t * x)) (Ioi 0) := by
    refine hExp.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)
  have hSplit :
      (∫ x : ℝ in Ioi 0,
        Real.exp (-a * x) * (1 - Real.cos (t * x))) =
        (∫ x : ℝ in Ioi 0, Real.exp (-a * x)) -
          ∫ x : ℝ in Ioi 0, Real.exp (-a * x) * Real.cos (t * x) := by
    rw [← integral_sub hExp hCos]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hSplit, integral_exp_mul_Ioi (a := -a) (by linarith) 0,
    integral_exp_neg_mul_cos_Ioi ha t]
  simp [ha.ne']

end Zeta23.CCM
