import Zeta23.ExceptionalZero.TwoTranslateDeterminant
import Zeta23.ExceptionalZero.TwoTranslateVisibility

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory ContinuousLinearMap
open scoped Convolution

/-!
# X4.5: fixed-test exclusion and a canonical radius detector family

X4 proves that universal determinant nonnegativity on the full real-even C² compact-support
class is exactly RH-strength.  This file deliberately does not repackage that universal
criterion.  Instead it isolates a weaker, test-by-test statement:

* if one fixed admissible test has nonnegative determinant gap at every nonnegative aperture,
  then that test cannot see any right-half zero;
* the target-adaptive X1 construction can be compressed to an explicit one-parameter family:
  normalized real-even bumps indexed only by a positive radius, followed by the already-proved
  pole killer;
* every spectral target is visible to some member of that radius family;
* consequently every hypothetical off-line zeta zero forces determinant failure for some fixed
  member of the canonical radius family.

This is a counterexample-exclusion interface.  It is not a proof of positivity for any fixed
detector, not a compact-uniform visibility theorem, and not a proof of RH.
-/

/-- Nonnegative two-translate determinant gap for one fixed test at every nonnegative aperture. -/
def FixedTestDeterminantNonnegative (k : ℝ → ℂ) : Prop :=
  ∀ a : ℝ, 0 ≤ a →
    0 ≤ twoTranslateDeterminantGap zetaZeroConfig k (2 * a)

/-- A fixed real-even admissible test with globally nonnegative determinant gap cannot see a
right-half zero.  This is the basic X4.5 zero-exclusion theorem. -/
theorem paperFT_eq_zero_at_right_zero_of_fixedTestDeterminantNonnegative
    {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k)
    (hreal : ∀ x : ℝ, (k x).im = 0)
    (heven : Function.Even k)
    (hdet : FixedTestDeterminantNonnegative k)
    (ρ₀ : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (ρ₀ : ℂ).re) :
    paperFT k (gammaOf (ρ₀ : ℂ)) = 0 := by
  by_contra hvis
  have hnot :=
    not_subexponential_weilRelativeCorrelation_of_right_zero
      hk hkc hreal heven ρ₀ hright hvis
  obtain ⟨a, ha, hgt⟩ :=
    exists_nonneg_gt_of_not_subexponential hnot ‖zetaZeroConfig.W k k‖
  have hneg :=
    twoTranslateDeterminantGap_neg_of_diagonal_norm_lt
      zetaZeroConfig k (2 * a) hgt
  exact (not_lt_of_ge (hdet a ha)) hneg

/-- Positive radii index the canonical detector family without carrying proof arguments separately. -/
abbrev PositiveRadius := {r : ℝ // 0 < r}

/-- Canonical normalized real bump with inner radius r/2 and outer radius r. -/
def canonicalRadiusBump (r : PositiveRadius) : ContDiffBump (0 : ℝ) :=
  ⟨(r : ℝ) / 2, (r : ℝ), by
    have hr : 0 < (r : ℝ) := r.2
    linarith, by
    have hr : 0 < (r : ℝ) := r.2
    linarith⟩

/-- Complex-valued real-even normalized seed associated to one radius. -/
def canonicalSeedTest (r : PositiveRadius) : ℝ → ℂ :=
  fun x => (((canonicalRadiusBump r).normed volume x : ℝ) : ℂ)

/-- Canonical pole-neutral detector associated to one radius. -/
def canonicalPoleKilledTest (r : PositiveRadius) : ℝ → ℂ :=
  poleKilled (canonicalSeedTest r)

/-- The canonical seed is C⁴. -/
theorem canonicalSeedTest_contDiff_four (r : PositiveRadius) :
    ContDiff ℝ 4 (canonicalSeedTest r) := by
  exact Complex.ofRealCLM.contDiff.comp (canonicalRadiusBump r).contDiff_normed

/-- The canonical seed is compactly supported. -/
theorem canonicalSeedTest_hasCompactSupport (r : PositiveRadius) :
    HasCompactSupport (canonicalSeedTest r) := by
  exact ((canonicalRadiusBump r).hasCompactSupport_normed (μ := volume)).comp_left
    (g := Complex.ofReal) Complex.ofReal_zero

/-- The canonical seed is even. -/
theorem canonicalSeedTest_even (r : PositiveRadius) :
    Function.Even (canonicalSeedTest r) := by
  intro x
  change (((canonicalRadiusBump r).normed volume (-x) : ℝ) : ℂ) =
    (((canonicalRadiusBump r).normed volume x : ℝ) : ℂ)
  rw [(canonicalRadiusBump r).normed_neg]

/-- The canonical seed is pointwise real. -/
theorem canonicalSeedTest_im_eq_zero (r : PositiveRadius) :
    ∀ x : ℝ, (canonicalSeedTest r x).im = 0 := by
  intro x
  simp [canonicalSeedTest]

/-- Every canonical pole-killed detector is an admissible C² compact-support real-even test. -/
theorem canonicalPoleKilledTest_admissible (r : PositiveRadius) :
    ContDiff ℝ 2 (canonicalPoleKilledTest r) ∧
      HasCompactSupport (canonicalPoleKilledTest r) ∧
      Function.Even (canonicalPoleKilledTest r) ∧
      (∀ x : ℝ, (canonicalPoleKilledTest r x).im = 0) := by
  have hq4 := canonicalSeedTest_contDiff_four r
  have hqc := canonicalSeedTest_hasCompactSupport r
  exact ⟨
    contDiff_poleKilled hq4,
    hasCompactSupport_poleKilled hqc,
    poleKilled_even (canonicalSeedTest_even r),
    poleKilled_im_eq_zero hq4 (canonicalSeedTest_im_eq_zero r)⟩

/-- Every canonical detector is pole-neutral at the two deterministic pole frequencies. -/
theorem canonicalPoleKilledTest_poleNeutral (r : PositiveRadius) :
    paperFT (canonicalPoleKilledTest r) (I / 2) = 0 ∧
      paperFT (canonicalPoleKilledTest r) (-I / 2) = 0 := by
  have hq4 := canonicalSeedTest_contDiff_four r
  have hq2 : ContDiff ℝ 2 (canonicalSeedTest r) := hq4.of_le (by norm_num)
  have hqc := canonicalSeedTest_hasCompactSupport r
  exact ⟨
    paperFT_poleKilled_I_half hq2 hqc,
    paperFT_poleKilled_neg_I_half hq2 hqc⟩

/-- The explicit radius family retains the X1 approximate-identity visibility mechanism:
every fixed complex spectral target is seen by at least one canonical seed radius. -/
theorem exists_canonicalSeed_radius_visible (w : ℂ) :
    ∃ r : PositiveRadius, paperFT (canonicalSeedTest r) w ≠ 0 := by
  let g : ℝ → ℝ := fun x => (Complex.exp (-(I * w * (x : ℂ)))).re
  have hg : Continuous g := by
    fun_prop
  have hg0 : ContinuousAt g 0 := hg.continuousAt
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.1 hg0) (1 / 2 : ℝ) (by norm_num)
  let φ : ContDiffBump (0 : ℝ) :=
    ⟨δ / 2, δ, by positivity, by linarith⟩
  have hconv :
      dist
          ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0)
          (g 0) ≤ (1 / 2 : ℝ) := by
    apply φ.dist_normed_convolution_le hg.aestronglyMeasurable
    intro x hx
    exact le_of_lt (hclose (by simpa [φ] using hx))
  have hconv_ne : ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0) ≠ 0 := by
    intro hzero
    rw [hzero] at hconv
    norm_num [g] at hconv
  let q : ℝ → ℂ := fun x => ((φ.normed volume x : ℝ) : ℂ)
  have hq4 : ContDiff ℝ 4 q := by
    exact Complex.ofRealCLM.contDiff.comp φ.contDiff_normed
  have hqc : HasCompactSupport q := by
    exact (φ.hasCompactSupport_normed (μ := volume)).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  have hint : Integrable (fun x : ℝ => q x * Complex.exp (I * w * (x : ℂ))) := by
    have hce : Continuous (fun x : ℝ => Complex.exp (I * w * (x : ℂ))) := by
      fun_prop
    exact (hq4.continuous.mul hce).integrable_of_hasCompactSupport hqc.mul_right
  have hconv_re :
      ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0) = (paperFT q w).re := by
    unfold MeasureTheory.convolution paperFT
    calc
      (∫ t : ℝ, ((lsmul ℝ ℝ) (φ.normed volume t)) (g (0 - t))) =
          ∫ u : ℝ, (q u * Complex.exp (I * w * (u : ℂ))).re := by
        apply integral_congr_ae
        filter_upwards with x
        simp [q, g, lsmul_apply, Complex.mul_re]
      _ = (∫ u : ℝ, q u * Complex.exp (I * w * (u : ℂ))).re := by
        exact integral_re hint
  have hqvis_re : (paperFT q w).re ≠ 0 := by
    intro hzero
    apply hconv_ne
    rw [hconv_re, hzero]
  have hqvis : paperFT q w ≠ 0 := by
    intro hzero
    apply hqvis_re
    rw [hzero]
    simp
  let r : PositiveRadius := ⟨δ, hδ⟩
  have hφ : φ = canonicalRadiusBump r := by
    rfl
  refine ⟨r, ?_⟩
  simpa [canonicalSeedTest, q, hφ] using hqvis

/-- Every nontrivial zeta zero is visible to some member of the canonical radius-indexed,
real-even, pole-neutral detector family. -/
theorem exists_canonicalPoleKilled_radius_visible
    (ρ₀ : zetaZeroConfig.carrier) :
    ∃ r : PositiveRadius,
      paperFT (canonicalPoleKilledTest r) (gammaOf (ρ₀ : ℂ)) ≠ 0 := by
  obtain ⟨r, hvis⟩ :=
    exists_canonicalSeed_radius_visible (gammaOf (ρ₀ : ℂ))
  have hq4 := canonicalSeedTest_contDiff_four r
  have hq2 : ContDiff ℝ 2 (canonicalSeedTest r) := hq4.of_le (by norm_num)
  have hqc := canonicalSeedTest_hasCompactSupport r
  refine ⟨r, ?_⟩
  exact paperFT_poleKilled_ne_zero_at_zero hq2 hqc ρ₀ hvis

/-- If a right-half zero exists, some fixed canonical detector has a negative determinant gap at
some nonnegative aperture. -/
theorem exists_canonicalRadius_negativeDeterminant_of_right_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (ρ₀ : ℂ).re) :
    ∃ r : PositiveRadius, ∃ a : ℝ,
      0 ≤ a ∧
        twoTranslateDeterminantGap zetaZeroConfig
          (canonicalPoleKilledTest r) (2 * a) < 0 := by
  obtain ⟨r, hvis⟩ := exists_canonicalPoleKilled_radius_visible ρ₀
  obtain ⟨hk, hkc, heven, hreal⟩ := canonicalPoleKilledTest_admissible r
  have hnot :=
    not_subexponential_weilRelativeCorrelation_of_right_zero
      hk hkc hreal heven ρ₀ hright hvis
  obtain ⟨a, ha, hgt⟩ :=
    exists_nonneg_gt_of_not_subexponential
      hnot ‖zetaZeroConfig.W (canonicalPoleKilledTest r) (canonicalPoleKilledTest r)‖
  refine ⟨r, a, ha, ?_⟩
  exact twoTranslateDeterminantGap_neg_of_diagonal_norm_lt
    zetaZeroConfig (canonicalPoleKilledTest r) (2 * a) hgt

/-- Canonical-family X4.5 endpoint: every hypothetical off-line zero forces determinant failure
for one fixed member of the radius-indexed detector family.  Reflection chooses the right-half
representative; the detector family itself is independent of that choice. -/
theorem exists_canonicalRadius_negativeDeterminant_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ r : PositiveRadius, ∃ a : ℝ,
      0 ≤ a ∧
        twoTranslateDeterminantGap zetaZeroConfig
          (canonicalPoleKilledTest r) (2 * a) < 0 := by
  obtain ⟨ρR, _hprov, hright⟩ :=
    exists_rightHalf_reflection_of_offLine ρ₀ hoff
  exact exists_canonicalRadius_negativeDeterminant_of_right_zero ρR hright

/-- Equivalent exclusion-language endpoint: an off-line zero forces at least one fixed canonical
detector to fail global nonnegative-aperture determinant positivity. -/
theorem exists_canonicalRadius_not_fixedTestDeterminantNonnegative_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ r : PositiveRadius,
      ¬ FixedTestDeterminantNonnegative (canonicalPoleKilledTest r) := by
  obtain ⟨r, a, ha, hneg⟩ :=
    exists_canonicalRadius_negativeDeterminant_of_offLine_zero ρ₀ hoff
  refine ⟨r, ?_⟩
  intro hfixed
  exact (not_lt_of_ge (hfixed a ha)) hneg

#print axioms Zeta23.ExceptionalZero.paperFT_eq_zero_at_right_zero_of_fixedTestDeterminantNonnegative
#print axioms Zeta23.ExceptionalZero.exists_canonicalSeed_radius_visible
#print axioms Zeta23.ExceptionalZero.exists_canonicalPoleKilled_radius_visible
#print axioms Zeta23.ExceptionalZero.exists_canonicalRadius_negativeDeterminant_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_canonicalRadius_not_fixedTestDeterminantNonnegative_of_offLine_zero

end Zeta23.ExceptionalZero
