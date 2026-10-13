import Zeta23.CCM.UniversalSincSourceTail
import Zeta23.CCM.UniversalSincBoxDensity

/-!
# An actual positive compact density candidate for the original convolution

The literal first-two-box density is convolved with the literal remaining
tail probability law. This constructs an actual real function; no density
properties are supplied as record premises. Positivity, continuity, mass
one and the prescribed support are established directly. Identifying its
measure with the full source law, its physical transform with the sinc
product and the smooth inverse candidate remains a separate connection.
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM.UniversalSinc

private theorem boxPairDensity_zero_of_abs_gt {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : a + b < |x|) : uniformBoxPairDensity a b x = 0 := by
  have hgap : min a (x + b) - max (-a) (x - b) ≤ 0 := by
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0] at hx
      have hmin := min_le_left a (x + b)
      have hmax := le_max_right (-a) (x - b)
      linarith
    · rw [abs_of_neg (lt_of_not_ge hx0)] at hx
      have hmin := min_le_right a (x + b)
      have hmax := le_max_left (-a) (x - b)
      linarith
  rw [uniformBoxPairDensity, max_eq_left hgap, zero_div]

private theorem boxPairDensity_le_height {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    uniformBoxPairDensity a b x ≤ 1 / (2 * a) := by
  have hgap : min a (x + b) - max (-a) (x - b) ≤ 2 * b := by
    have hmin := min_le_right a (x + b)
    have hmax := le_max_right (-a) (x - b)
    linarith
  have hmax : max 0 (min a (x + b) - max (-a) (x - b)) ≤ 2 * b :=
    max_le (by positivity) hgap
  unfold uniformBoxPairDensity
  apply (div_le_iff₀ (by positivity : 0 < 4 * a * b)).mpr
  calc
    _ ≤ 2 * b := hmax
    _ = (1 / (2 * a)) * (4 * a * b) := by field_simp <;> ring

private theorem original_first_two_widths (s : ℝ) :
    width s 0 + width s 1 = 2 * s / 3 := by
  norm_num [width] <;> ring

theorem originalBoxPairDensity_nonneg {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 ≤ originalBoxPairDensity s x :=
  uniformBoxPairDensity_nonneg (width_pos hs 0) (width_pos hs 1) x

private theorem originalBoxPairDensity_norm_le {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ‖originalBoxPairDensity s x‖ ≤ 1 / (2 * width s 0) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (originalBoxPairDensity_nonneg hs x)]
  exact boxPairDensity_le_height (width_pos hs 0) (width_pos hs 1) x

theorem continuous_originalBoxPairDensity (s : ℝ) :
    Continuous (originalBoxPairDensity s) := continuous_uniformBoxPairDensity _ _

/-- The original two-box convolution averaged over its actual infinite tail. -/
def originalDensityCandidate (s x : ℝ) : ℝ :=
  ∫ y : ℝ, originalBoxPairDensity s (x - y) ∂originalSourceTailLaw s 2

theorem originalDensityCandidate_nonneg {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 ≤ originalDensityCandidate s x := by
  exact integral_nonneg (fun y => originalBoxPairDensity_nonneg hs (x - y))

theorem continuous_originalDensityCandidate {s : ℝ} (hs : 0 < s) :
    Continuous (originalDensityCandidate s) := by
  letI : IsProbabilityMeasure (originalSourceTailLaw s 2) :=
    originalSourceTailLaw_isProbabilityMeasure hs.le 2
  apply continuous_of_dominated
    (bound := fun _ : ℝ => 1 / (2 * width s 0))
  · intro x
    exact ((continuous_originalBoxPairDensity s).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro x
    exact ae_of_all _ (fun y => originalBoxPairDensity_norm_le hs (x - y))
  · exact integrable_const _
  · exact ae_of_all _ (fun y => (continuous_originalBoxPairDensity s).comp
      (continuous_id.sub continuous_const))

private theorem originalSourceTailLaw_ae_support {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ y ∂originalSourceTailLaw s 2, |y| ≤ s / 3 := by
  unfold originalSourceTailLaw
  apply (ae_map_iff (measurable_sourceSampleTail hs 2).aemeasurable
    (measurableSet_le continuous_abs.measurable measurable_const)).mpr
  filter_upwards with ω
  simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num] using
    sourceSampleTail_abs_le hs 2 ω

theorem originalDensityCandidate_zero_of_abs_gt {s x : ℝ} (hs : 0 < s) (hx : s < |x|) :
    originalDensityCandidate s x = 0 := by
  unfold originalDensityCandidate
  apply integral_eq_zero_of_ae
  filter_upwards [originalSourceTailLaw_ae_support hs.le] with y hy
  have htriangle : |x| ≤ |x - y| + |y| := by
    simpa only [sub_add_cancel] using abs_add_le (x - y) y
  have hgap : width s 0 + width s 1 < |x - y| := by
    rw [original_first_two_widths]
    linarith
  exact boxPairDensity_zero_of_abs_gt (width_pos hs 0) (width_pos hs 1) hgap

theorem originalDensityCandidate_hasCompactSupport {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (originalDensityCandidate s) := by
  apply HasCompactSupport.intro (K := Icc (-s) s) isCompact_Icc
  intro x hx
  apply originalDensityCandidate_zero_of_abs_gt hs
  exact lt_of_not_ge (fun h => hx (abs_le.mp h))

theorem integrable_originalDensityCandidate {s : ℝ} (hs : 0 < s) :
    Integrable (originalDensityCandidate s) :=
  (continuous_originalDensityCandidate hs).integrable_of_hasCompactSupport
    (originalDensityCandidate_hasCompactSupport hs)

theorem originalDensityCandidate_joint_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => originalBoxPairDensity s (p.2 - p.1))
      ((originalSourceTailLaw s 2).prod volume) := by
  letI : IsProbabilityMeasure (originalSourceTailLaw s 2) :=
    originalSourceTailLaw_isProbabilityMeasure hs.le 2
  have hprefix : Integrable (originalBoxPairDensity s) :=
    integrable_uniformBoxPairDensity (width_pos hs 0) (width_pos hs 1)
  have hm : Continuous (fun p : ℝ × ℝ => originalBoxPairDensity s (p.2 - p.1)) :=
    (continuous_originalBoxPairDensity s).comp (continuous_snd.sub continuous_fst)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun y => hprefix.comp_sub_right y)
  · have heq : (fun y : ℝ => ∫ x : ℝ, ‖originalBoxPairDensity s (x - y)‖) =
        (fun _ : ℝ => (1 : ℝ)) := by
      funext y
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (originalBoxPairDensity_nonneg hs _)]
      rw [integral_sub_right_eq_self]
      exact integral_uniformBoxPairDensity (width_pos hs 0) (width_pos hs 1)
    rw [heq]
    exact integrable_const 1

/-- Exact mass follows from actual translation-invariant integrals and
Fubini, justified by the proved integrable joint prefix/tail function. -/
theorem integral_originalDensityCandidate {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, originalDensityCandidate s x) = 1 := by
  letI : IsProbabilityMeasure (originalSourceTailLaw s 2) :=
    originalSourceTailLaw_isProbabilityMeasure hs.le 2
  unfold originalDensityCandidate
  rw [← integral_integral_swap (originalDensityCandidate_joint_integrable hs)]
  have hinner : ∀ y : ℝ, (∫ x : ℝ, originalBoxPairDensity s (x - y)) = 1 := by
    intro y
    rw [integral_sub_right_eq_self]
    exact integral_uniformBoxPairDensity (width_pos hs 0) (width_pos hs 1)
  simp_rw [hinner]
  simp

end Zeta23.CCM.UniversalSinc

#print axioms Zeta23.CCM.UniversalSinc.originalDensityCandidate_nonneg
#print axioms Zeta23.CCM.UniversalSinc.continuous_originalDensityCandidate
#print axioms Zeta23.CCM.UniversalSinc.originalDensityCandidate_hasCompactSupport
#print axioms Zeta23.CCM.UniversalSinc.integral_originalDensityCandidate
