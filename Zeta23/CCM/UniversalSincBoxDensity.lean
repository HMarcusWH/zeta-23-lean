import Zeta23.CCM.UniversalSincDetector
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The actual first two box densities in the original convolution

The first two prescribed widths are unequal. Their actual density is the
normalized interval-overlap trapezoid below. The convolution identity,
continuity, positivity and mass are proved for the literal boxes. This is
a density precursor; it does not identify the full infinite source law or
the smooth inverse-Fourier candidate.
-/

noncomputable section

open Set MeasureTheory ContinuousLinearMap
open scoped Topology Convolution

namespace Zeta23.CCM.UniversalSinc

def uniformBoxDensity (a : ℝ) : ℝ → ℝ :=
  (Icc (-a) a).indicator (fun _ => 1 / (2 * a))

theorem uniformBoxDensity_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 ≤ uniformBoxDensity a x := by
  unfold uniformBoxDensity
  exact Set.indicator_nonneg (fun _ _ => by positivity) x

theorem integrable_uniformBoxDensity (a : ℝ) : Integrable (uniformBoxDensity a) := by
  unfold uniformBoxDensity
  apply IntegrableOn.integrable_indicator
  · exact integrableOn_const (by rw [Real.volume_Icc]; simp) (by finiteness)
  · exact measurableSet_Icc

theorem integral_uniformBoxDensity {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, uniformBoxDensity a x) = 1 := by
  unfold uniformBoxDensity
  rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ a - -a), smul_eq_mul]
  field_simp
  ring

/-- Literal overlap of the two original centered intervals; unequal boxes
give a trapezoid rather than the equal-width triangular special case. -/
def uniformBoxPairDensity (a b x : ℝ) : ℝ :=
  max 0 (min a (x + b) - max (-a) (x - b)) / (4 * a * b)

theorem uniformBoxPairDensity_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ uniformBoxPairDensity a b x := by
  unfold uniformBoxPairDensity
  positivity

theorem continuous_uniformBoxPairDensity (a b : ℝ) : Continuous (uniformBoxPairDensity a b) := by
  unfold uniformBoxPairDensity
  fun_prop

private theorem box_overlap_mem (a b x y : ℝ) :
    y ∈ Icc (max (-a) (x - b)) (min a (x + b)) ↔
      y ∈ Icc (-a) a ∧ x - y ∈ Icc (-b) b := by
  simp only [mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, h3⟩, by constructor <;> linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩

private theorem box_product_eq_overlap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    uniformBoxDensity a y * uniformBoxDensity b (x - y) =
      (Icc (max (-a) (x - b)) (min a (x + b))).indicator
        (fun _ : ℝ => 1 / (4 * a * b)) y := by
  have hmem := box_overlap_mem a b x y
  by_cases h1 : y ∈ Icc (-a) a <;> by_cases h2 : x - y ∈ Icc (-b) b
  all_goals simp only [uniformBoxDensity, Set.indicator_apply, hmem, h1, h2,
    and_self, and_false, false_and, if_true, if_false, mul_zero, zero_mul]
  field_simp
  ring

private theorem real_volume_interval (u v : ℝ) :
    volume.real (Icc u v) = max 0 (v - u) := by
  rw [measureReal_def, Real.volume_Icc]
  by_cases h : 0 ≤ v - u
  · rw [ENNReal.toReal_ofReal h, max_eq_right h]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h), ENNReal.toReal_zero,
      max_eq_left (le_of_not_ge h)]

/-- Exact pointwise identity with the convolution of the unchanged boxes. -/
theorem uniformBoxPairDensity_eq_convolution {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    uniformBoxPairDensity a b = uniformBoxDensity a ⋆[mul ℝ ℝ, volume] uniformBoxDensity b := by
  funext x
  change uniformBoxPairDensity a b x =
    ∫ y : ℝ, uniformBoxDensity a y * uniformBoxDensity b (x - y)
  simp_rw [box_product_eq_overlap ha hb]
  rw [integral_indicator_const _ measurableSet_Icc, real_volume_interval, smul_eq_mul]
  unfold uniformBoxPairDensity
  ring

theorem integrable_uniformBoxPairDensity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (uniformBoxPairDensity a b) := by
  rw [uniformBoxPairDensity_eq_convolution ha hb]
  exact (integrable_uniformBoxDensity a).integrable_convolution (mul ℝ ℝ)
    (integrable_uniformBoxDensity b)

theorem integral_uniformBoxPairDensity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, uniformBoxPairDensity a b x) = 1 := by
  rw [uniformBoxPairDensity_eq_convolution ha hb,
    integral_convolution (mul ℝ ℝ) (integrable_uniformBoxDensity a) (integrable_uniformBoxDensity b),
    integral_uniformBoxDensity ha, integral_uniformBoxDensity hb]
  simp

/-- The specified initial pair, retaining its exact unequal widths. -/
def originalBoxPairDensity (s : ℝ) : ℝ → ℝ :=
  uniformBoxPairDensity (width s 0) (width s 1)

theorem originalBoxPairDensity_positive_normalized {s : ℝ} (hs : 0 < s) :
    Continuous (originalBoxPairDensity s) ∧
      (∀ x : ℝ, 0 ≤ originalBoxPairDensity s x) ∧
      (∫ x : ℝ, originalBoxPairDensity s x) = 1 := by
  exact ⟨continuous_uniformBoxPairDensity _ _,
    uniformBoxPairDensity_nonneg (width_pos hs 0) (width_pos hs 1),
    integral_uniformBoxPairDensity (width_pos hs 0) (width_pos hs 1)⟩

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.uniformBoxPairDensity_eq_convolution
#print axioms Zeta23.CCM.UniversalSinc.originalBoxPairDensity_positive_normalized
