import Mathlib.Analysis.MellinInversion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The exact Mellin transform and inverse of the literal prime-ramp kernel.
These results reduce right-line Perron inversion to a Dirichlet-series
interchange. They use only Mathlib and do not assert any zero-free strip.
-/

set_option autoImplicit false

noncomputable section

open Set Complex MeasureTheory

namespace Zeta23.RHReference

/-- The literal ramp as a function of the ratio n/x. -/
def perronRamp (y : ℝ) : ℂ := (max (y⁻¹ - 1) 0 : ℝ)

def perronRampTransform (s : ℂ) : ℂ := 1 / (s * (s - 1))

theorem perronRamp_continuousAt {y : ℝ} (hy : 0 < y) :
    ContinuousAt perronRamp y := by
  unfold perronRamp
  exact Complex.continuous_ofReal.continuousAt.comp
    (((continuousAt_id.inv₀ hy.ne').sub continuousAt_const).max continuousAt_const)

theorem perronRamp_eq_indicator_sub {y : ℝ} (hy : 0 < y) :
    perronRamp y =
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) y -
      indicator (Ioc 0 1) (fun _ : ℝ => (1 : ℂ)) y := by
  by_cases h : y ≤ 1
  · have hmem : y ∈ Ioc (0 : ℝ) 1 := ⟨hy, h⟩
    have hinv : 1 ≤ y⁻¹ := (one_le_inv₀ hy).2 h
    simp [perronRamp, max_eq_left (sub_nonneg.mpr hinv), hmem, Complex.cpow_neg_one]
  · have hmem : y ∉ Ioc (0 : ℝ) 1 := fun hmem => h hmem.2
    have hinv : y⁻¹ ≤ 1 := (inv_le_one₀ hy).2 (le_of_not_ge h)
    simp [perronRamp, max_eq_right (sub_nonpos.mpr hinv), hmem]

/-- Integral over (0,1] of y^(s-1)(y⁻¹-1) = 1/[s(s-1)]. -/
theorem hasMellin_perronRamp {s : ℂ} (hs : 1 < s.re) :
    HasMellin perronRamp s (perronRampTransform s) := by
  have ha := hasMellin_cpow_Ioc (-1 : ℂ) (s := s) (by simp; linarith)
  have hb := hasMellin_one_Ioc (s := s) (by linarith)
  have h := hasMellin_sub ha.1 hb.1
  have hc : (1 : ℂ) / (s + (-1 : ℂ)) - 1 / s = perronRampTransform s := by
    have hs0 : s ≠ 0 := fun heq => by norm_num [heq] at hs
    have hs1 : s - 1 ≠ 0 := fun heq => by
      have h1 : s = 1 := sub_eq_zero.mp heq
      simp [h1] at hs
    rw [← sub_eq_add_neg]
    unfold perronRampTransform
    field_simp
    ring
  have heq : EqOn perronRamp
      (fun y => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) y -
        indicator (Ioc 0 1) (fun _ : ℝ => (1 : ℂ)) y) (Ioi 0) :=
    fun y hy => perronRamp_eq_indicator_sub hy
  have hweight : EqOn
      (fun y : ℝ => (y : ℂ) ^ (s - 1) • perronRamp y)
      (fun y : ℝ => (y : ℂ) ^ (s - 1) •
        (indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) y -
        indicator (Ioc 0 1) (fun _ : ℝ => (1 : ℂ)) y)) (Ioi 0) :=
    fun y hy => congrArg (fun z : ℂ => (y : ℂ) ^ (s - 1) • z) (heq hy)
  refine ⟨(integrableOn_congr_fun hweight measurableSet_Ioi).2 h.1, ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hweight]
  exact h.2.trans ((congrArg₂ (· - ·) ha.2 hb.2).trans hc)

private theorem norm_vertical_two_sub_one_sq (t : ℝ) :
    ‖(2 : ℂ) + t * I - 1‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

private theorem norm_vertical_two_sq (t : ℝ) :
    ‖(2 : ℂ) + t * I‖ ^ 2 = 4 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem norm_perronRampTransform_vertical_two (t : ℝ) :
    ‖perronRampTransform (2 + t * I)‖ ≤ (1 + t ^ 2)⁻¹ := by
  have hn : ‖(2 : ℂ) + t * I - 1‖ ≤ ‖(2 : ℂ) + t * I‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [norm_vertical_two_sub_one_sq, norm_vertical_two_sq]
    linarith
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hmul : 1 + t ^ 2 ≤ ‖(2 : ℂ) + t * I‖ * ‖(2 : ℂ) + t * I - 1‖ := by
    rw [← norm_vertical_two_sub_one_sq, pow_two]
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  simp only [perronRampTransform, one_div, norm_inv, norm_mul]
  exact inv_anti₀ hp hmul

theorem verticalIntegrable_perronRampTransform :
    Complex.VerticalIntegrable perronRampTransform 2 := by
  apply integrable_inv_one_add_sq.mono'
  · unfold perronRampTransform
    have hpoly : Continuous (fun t : ℝ => ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I - 1)) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).mul
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const)
    have hn (t : ℝ) : ((2 : ℂ) + t * I) * ((2 : ℂ) + t * I - 1) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · intro h
        have := congrArg Complex.re h
        norm_num at this
      · intro h
        have := congrArg Complex.re h
        norm_num at this
    exact (continuous_const.div hpoly hn).aestronglyMeasurable
  · exact Filter.Eventually.of_forall norm_perronRampTransform_vertical_two

/-- Inversion at the specific line Re s = 2 with all convergence checked. -/
theorem mellinInv_perronRampTransform {y : ℝ} (hy : 0 < y) :
    mellinInv 2 perronRampTransform y = perronRamp y := by
  have hh (t : ℝ) : mellin perronRamp (((2 : ℝ) : ℂ) + t * I) =
      perronRampTransform (((2 : ℝ) : ℂ) + t * I) :=
    (hasMellin_perronRamp (by norm_num : 1 < (((2 : ℝ) : ℂ) + t * I).re)).2
  have hVert : Complex.VerticalIntegrable (mellin perronRamp) 2 := by
    unfold Complex.VerticalIntegrable
    simp_rw [hh]
    exact verticalIntegrable_perronRampTransform
  have hi := mellinInv_mellin_eq 2 perronRamp hy
    (hasMellin_perronRamp (by norm_num : 1 < (2 : ℂ).re)).1 hVert
    (perronRamp_continuousAt hy)
  simpa only [mellinInv, hh] using hi

#print axioms Zeta23.RHReference.hasMellin_perronRamp
#print axioms Zeta23.RHReference.verticalIntegrable_perronRampTransform
#print axioms Zeta23.RHReference.mellinInv_perronRampTransform

end Zeta23.RHReference
