import Zeta23.CCM.DictionaryArchBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators

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
  simp

/-- Physical-space summand normalized so that no later `x ↦ 2x` substitution is
needed: its integral is exactly the digamma summand at `τ/2`. -/
def archPhysicalSeriesTerm (τ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  2 * Real.exp (-(2 * ((m : ℝ) + 1 / 4)) * x) * (1 - Real.cos (τ * x))

/-- Each physical summand is nonnegative. -/
theorem archPhysicalSeriesTerm_nonneg (τ : ℝ) (m : ℕ) (x : ℝ) :
    0 ≤ archPhysicalSeriesTerm τ m x := by
  have hcos : Real.cos (τ * x) ≤ 1 := Real.cos_le_one (τ * x)
  have hsub : 0 ≤ 1 - Real.cos (τ * x) := sub_nonneg.mpr hcos
  unfold archPhysicalSeriesTerm
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hsub

/-- Each physical summand is integrable on the positive half-line. -/
theorem integrableOn_archPhysicalSeriesTerm (τ : ℝ) (m : ℕ) :
    IntegrableOn (archPhysicalSeriesTerm τ m) (Ioi 0) := by
  let a : ℝ := 2 * ((m : ℝ) + 1 / 4)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hExp : IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Ioi 0) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
  have hCos : IntegrableOn
      (fun x : ℝ => Real.exp (-a * x) * Real.cos (τ * x)) (Ioi 0) := by
    refine hExp.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (τ * x)
  have hSub : IntegrableOn
      (fun x : ℝ => Real.exp (-a * x) * (1 - Real.cos (τ * x))) (Ioi 0) := by
    have heq :
        (fun x : ℝ => Real.exp (-a * x) * (1 - Real.cos (τ * x))) =
          fun x => Real.exp (-a * x) - Real.exp (-a * x) * Real.cos (τ * x) := by
      funext x
      ring
    rw [heq]
    exact hExp.sub hCos
  have heq : archPhysicalSeriesTerm τ m =
      fun x => 2 * (Real.exp (-a * x) * (1 - Real.cos (τ * x))) := by
    funext x
    dsimp [archPhysicalSeriesTerm, a]
    ring
  rw [heq]
  exact hSub.const_mul 2

/-- The integral of one physical summand is the corresponding positive-abscissa
digamma term. -/
theorem integral_archPhysicalSeriesTerm_Ioi (τ : ℝ) (m : ℕ) :
    (∫ x : ℝ in Ioi 0, archPhysicalSeriesTerm τ m x) =
      archDigammaAllTerm (τ / 2) m := by
  let a : ℝ := 2 * ((m : ℝ) + 1 / 4)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have h := integral_exp_neg_mul_one_sub_cos_Ioi ha τ
  calc
    (∫ x : ℝ in Ioi 0, archPhysicalSeriesTerm τ m x) =
        ∫ x : ℝ in Ioi 0,
          2 * (Real.exp (-a * x) * (1 - Real.cos (τ * x))) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [archPhysicalSeriesTerm, a]
      ring
    _ = 2 * (1 / a - a / (a ^ 2 + τ ^ 2)) := by
      rw [integral_const_mul, h]
    _ = archDigammaAllTerm (τ / 2) m := by
      unfold archDigammaAllTerm
      dsimp [a]
      have hb : (m : ℝ) + 1 / 4 ≠ 0 := by positivity
      have hden1 :
          (2 * ((m : ℝ) + 1 / 4)) ^ 2 + τ ^ 2 ≠ 0 := by positivity
      have hden2 :
          ((m : ℝ) + 1 / 4) ^ 2 + (τ / 2) ^ 2 ≠ 0 := by positivity
      field_simp [hb, hden1, hden2]

/-- Norm integrals equal the same digamma terms because the physical summands are
pointwise nonnegative. -/
theorem integral_norm_archPhysicalSeriesTerm_Ioi (τ : ℝ) (m : ℕ) :
    (∫ x : ℝ in Ioi 0, ‖archPhysicalSeriesTerm τ m x‖) =
      archDigammaAllTerm (τ / 2) m := by
  calc
    (∫ x : ℝ in Ioi 0, ‖archPhysicalSeriesTerm τ m x‖) =
        ∫ x : ℝ in Ioi 0, archPhysicalSeriesTerm τ m x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (archPhysicalSeriesTerm_nonneg τ m x)]
    _ = archDigammaAllTerm (τ / 2) m := integral_archPhysicalSeriesTerm_Ioi τ m

/-- Absolute integrals of the physical summands form a summable family. -/
theorem summable_integral_norm_archPhysicalSeriesTerm (τ : ℝ) :
    Summable (fun m : ℕ => ∫ x : ℝ in Ioi 0, ‖archPhysicalSeriesTerm τ m x‖) := by
  refine (summable_archDigammaAllTerm (τ / 2)).congr ?_
  intro m
  exact (integral_norm_archPhysicalSeriesTerm_Ioi τ m).symm

/-- Certified Tonelli/Fubini gate for the physical digamma series. -/
theorem tsum_integral_archPhysicalSeriesTerm_eq_integral_tsum (τ : ℝ) :
    (∑' m : ℕ, ∫ x : ℝ in Ioi 0, archPhysicalSeriesTerm τ m x) =
      ∫ x : ℝ in Ioi 0, ∑' m : ℕ, archPhysicalSeriesTerm τ m x := by
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun m => integrableOn_archPhysicalSeriesTerm τ m)
    (summable_integral_norm_archPhysicalSeriesTerm τ)

end Zeta23.CCM
