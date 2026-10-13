import Zeta23.CCM.UniversalSincSourceComplexTransform
import Zeta23.CCM.UniversalSincSourceSymmetry
import Zeta23.ExceptionalZero.UniversalSincDetectorVisibility
import Zeta23.ExceptionalZero.TwoTranslateVisibility
import Zeta23.ExceptionalZero.TwoTranslateCorrelation
import Zeta23.Poisson.PaperFTConvolution

/-!
# The actual original pole-killed physical detector

The functions below are the literal source density and its first two
applications of `P = ∂² - 1/4`. Their transforms, regularity, support and
off-line visibility are derived from the constructed source. The
correlation coefficient is retained as a complex square. The inherited
norm-growth obstruction is not the two-sided signed phase-depth theorem.
-/

noncomputable section

open MeasureTheory Complex ContinuousLinearMap
open scoped Topology Convolution

namespace Zeta23.ExceptionalZero

/-- The original physical detector `k_s = P q_s`. -/
def originalSincTest (s : ℝ) : ℝ → ℂ :=
  poleKilled (CCM.UniversalSinc.originalDensityComplex s)

/-- The original twice-differentiated source `j_s = P² q_s`. -/
def originalSincSecondTest (s : ℝ) : ℝ → ℂ :=
  poleKilled (originalSincTest s)

private theorem contDiff_actual_source {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (CCM.UniversalSinc.originalDensityComplex s) := by
  rw [← CCM.UniversalSinc.inverseCandidate_eq_originalDensityComplex hs]
  exact CCM.UniversalSinc.contDiff_inverseCandidate hs

private theorem contDiff_poleKilled_infty {q : ℝ → ℂ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) : ContDiff ℝ (⊤ : ℕ∞) (poleKilled q) := by
  have hd := (contDiff_infty_iff_deriv.mp hq).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact hdd.sub (contDiff_const.mul hq)

theorem contDiff_originalSincTest {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (originalSincTest s) :=
  contDiff_poleKilled_infty (contDiff_actual_source hs)

theorem contDiff_originalSincSecondTest {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ (⊤ : ℕ∞) (originalSincSecondTest s) :=
  contDiff_poleKilled_infty (contDiff_originalSincTest hs)

theorem hasCompactSupport_originalSincTest {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (originalSincTest s) :=
  hasCompactSupport_poleKilled (CCM.UniversalSinc.originalDensityComplex_hasCompactSupport hs)

theorem hasCompactSupport_originalSincSecondTest {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (originalSincSecondTest s) :=
  hasCompactSupport_poleKilled (hasCompactSupport_originalSincTest hs)

theorem originalSincTest_even {s : ℝ} (hs : 0 < s) :
    Function.Even (originalSincTest s) :=
  poleKilled_even (CCM.UniversalSinc.originalDensityComplex_even hs)

theorem originalSincSecondTest_even {s : ℝ} (hs : 0 < s) :
    Function.Even (originalSincSecondTest s) := poleKilled_even (originalSincTest_even hs)

theorem originalSincTest_im_eq_zero {s : ℝ} (hs : 0 < s) :
    ∀ x : ℝ, (originalSincTest s x).im = 0 :=
  poleKilled_im_eq_zero ((contDiff_actual_source hs).of_le (by norm_num))
    (CCM.UniversalSinc.originalDensityComplex_im s)

theorem originalSincSecondTest_im_eq_zero {s : ℝ} (hs : 0 < s) :
    ∀ x : ℝ, (originalSincSecondTest s x).im = 0 :=
  poleKilled_im_eq_zero ((contDiff_originalSincTest hs).of_le (by norm_num))
    (originalSincTest_im_eq_zero hs)

/-- The physical detector has the exact original multiplier at every
complex frequency, with the paper's forward sign and normalization. -/
theorem paperFT_originalSincTest {s : ℝ} (hs : 0 < s) (z : ℂ) :
    paperFT (originalSincTest s) z = originalSincMultiplier s z := by
  unfold originalSincTest originalSincMultiplier
  rw [paperFT_poleKilled ((contDiff_actual_source hs).of_le (by norm_num))
    (CCM.UniversalSinc.originalDensityComplex_hasCompactSupport hs),
    CCM.UniversalSinc.paperFT_originalDensityComplex hs]

theorem paperFT_originalSincSecondTest {s : ℝ} (hs : 0 < s) (z : ℂ) :
    paperFT (originalSincSecondTest s) z =
      (z ^ 2 + 1 / 4) ^ 2 * CCM.UniversalSinc.product s z := by
  unfold originalSincSecondTest
  rw [paperFT_poleKilled ((contDiff_originalSincTest hs).of_le (by norm_num))
    (hasCompactSupport_originalSincTest hs), paperFT_originalSincTest hs]
  unfold originalSincMultiplier
  ring

theorem paperFT_originalSincTest_elementary_pair {s : ℝ} (hs : 0 < s) :
    paperFT (originalSincTest s) (I / 2) = 0 ∧
      paperFT (originalSincTest s) (-I / 2) = 0 := by
  rw [paperFT_originalSincTest hs, paperFT_originalSincTest hs]
  exact ⟨originalSincMultiplier_I_half s, originalSincMultiplier_neg_I_half s⟩

/-- Visibility is derived for the physical test from its actual transform;
no visibility or source-Fourier certificate is accepted as a premise. -/
theorem paperFT_originalSincTest_ne_zero_at_off_line_zero {s : ℝ} (hs : 0 < s)
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    paperFT (originalSincTest s) (gammaOf (ρ : ℂ)) ≠ 0 := by
  rw [paperFT_originalSincTest hs]
  exact originalSincMultiplier_ne_zero_at_off_line_zero hs ρ hoff

/-- The physical correlation transform is the complex square, including
nonreal arguments. -/
theorem paperFT_originalSincTest_self_convolution {s : ℝ} (hs : 0 < s) (z : ℂ) :
    paperFT (originalSincTest s ⋆[mul ℂ ℂ, volume] originalSincTest s) z =
      originalSincMultiplier s z ^ 2 := by
  rw [Zeta23.paperFT_mul_convolution_eq_of_continuous_compactSupport
    (contDiff_originalSincTest hs).continuous (hasCompactSupport_originalSincTest hs)
    (contDiff_originalSincTest hs).continuous (hasCompactSupport_originalSincTest hs),
    paperFT_originalSincTest hs]
  ring

theorem fixed_originalSincTest_square_ne_zero_at_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    paperFT (originalSincTest CCM.UniversalSinc.fixedScale) (gammaOf (ρ : ℂ)) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (paperFT_originalSincTest_ne_zero_at_off_line_zero
    CCM.UniversalSinc.fixedScale_pos ρ hoff)

theorem absolutelySummable_originalSincSquaredFilter {s : ℝ} (hs : 0 < s) :
    AbsolutelySummableZeroFilter (squaredWeilZeroFilter (originalSincTest s)) :=
  absolutelySummableZeroFilter_squaredWeil
    ((contDiff_originalSincTest hs).of_le (by norm_num))
    (hasCompactSupport_originalSincTest hs)

theorem originalSincCorrelation_eq_filteredSquaredFamily {s : ℝ} (hs : 0 < s) (a : ℝ) :
    weilRelativeCorrelation zetaZeroConfig (originalSincTest s) (2 * a) =
      filteredZeroFamily (squaredWeilZeroFilter (originalSincTest s)) (1 / 2 : ℂ) a :=
  weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared
    (originalSincTest_im_eq_zero hs) (originalSincTest_even hs) a

/-- The actual fixed correlation has a visible exposed pole and fails a
norm subexponential bound. Two separate signed late excursions still
require their own argument. -/
theorem fixed_originalSincCorrelation_not_subexponential_of_right_zero
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re) :
    ¬ Subexponential (fun a =>
      ‖weilRelativeCorrelation zetaZeroConfig
        (originalSincTest CCM.UniversalSinc.fixedScale) (2 * a)‖) := by
  have hcoeff : zeroFilterCoeff
      (squaredWeilZeroFilter (originalSincTest CCM.UniversalSinc.fixedScale)) ρ ≠ 0 := by
    rw [zeroFilterCoeff_squaredWeilZeroFilter]
    refine mul_ne_zero ?_
      (fixed_originalSincTest_square_ne_zero_at_off_line_zero ρ (ne_of_gt hright))
    have hm : 1 ≤ zeroMult (ρ : ℂ) := zetaZeroConfig.one_le_mult _ ρ.2
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  have hmain := not_subexponential_filteredZeroFamily_of_right_zero
    (absolutelySummable_originalSincSquaredFilter CCM.UniversalSinc.fixedScale_pos)
    (by norm_num : (1 / 2 : ℂ).re = 1 / 2) ρ hright hcoeff
  have heq : (fun a => ‖weilRelativeCorrelation zetaZeroConfig
        (originalSincTest CCM.UniversalSinc.fixedScale) (2 * a)‖) =
      (fun a => ‖filteredZeroFamily
        (squaredWeilZeroFilter (originalSincTest CCM.UniversalSinc.fixedScale))
        (1 / 2 : ℂ) a‖) := by
    funext a
    rw [originalSincCorrelation_eq_filteredSquaredFamily CCM.UniversalSinc.fixedScale_pos]
  rw [heq]
  exact hmain

/-- The existing exposed-pole theorem now consumes the same fixed physical
source. This norm-growth obstruction does not assert signed phase depth. -/
theorem fixed_originalSincTest_not_subexponential_of_right_zero
    (ρ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ : ℂ).re) :
    ¬ Subexponential (fun a =>
      ‖Zeta23.EF.literatureRHS
        (translateRight (originalSincTest CCM.UniversalSinc.fixedScale) (2 * a))‖) := by
  exact not_subexponential_weilLiteratureRHS_of_right_zero
    ((contDiff_originalSincTest CCM.UniversalSinc.fixedScale_pos).of_le (by norm_num))
    (hasCompactSupport_originalSincTest CCM.UniversalSinc.fixedScale_pos) ρ hright
    (paperFT_originalSincTest_ne_zero_at_off_line_zero CCM.UniversalSinc.fixedScale_pos
      ρ (ne_of_gt hright))

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.paperFT_originalSincTest
#print axioms Zeta23.ExceptionalZero.paperFT_originalSincSecondTest
#print axioms Zeta23.ExceptionalZero.paperFT_originalSincTest_self_convolution
#print axioms Zeta23.ExceptionalZero.fixed_originalSincTest_square_ne_zero_at_off_line_zero
#print axioms Zeta23.ExceptionalZero.absolutelySummable_originalSincSquaredFilter
#print axioms Zeta23.ExceptionalZero.originalSincCorrelation_eq_filteredSquaredFamily
#print axioms Zeta23.ExceptionalZero.fixed_originalSincCorrelation_not_subexponential_of_right_zero
#print axioms Zeta23.ExceptionalZero.fixed_originalSincTest_not_subexponential_of_right_zero
