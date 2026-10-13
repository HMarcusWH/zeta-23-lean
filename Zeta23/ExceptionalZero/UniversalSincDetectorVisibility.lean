import Zeta23.CCM.UniversalSincDetector
import Zeta23.ExceptionalZero.WeilFilter

/-!
# The original product multiplier at actual off-line zeros

This is the algebraic visibility component for the exact infinite sinc
product. It does not identify that product with `paperFT q`: constructing
the infinite-convolution density and proving its transform identity remain
necessary before the physical detector visibility theorem is available.
-/

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-- The transform multiplier prescribed by the paper source construction. -/
def originalSincMultiplier (s : ℝ) (z : ℂ) : ℂ :=
  -(z ^ 2 + 1 / 4) * CCM.UniversalSinc.product s z

theorem originalSincMultiplier_gammaOf (s : ℝ) (ρ : ℂ) :
    originalSincMultiplier s (gammaOf ρ) =
      ρ * (ρ - 1) * CCM.UniversalSinc.product s (gammaOf ρ) := by
  unfold originalSincMultiplier
  rw [poleKiller_factor_eq]

/-- No visibility premise is accepted: nonvanishing follows from the proved
infinite-product criterion and the actual open-strip zero carrier. -/
theorem originalSincMultiplier_ne_zero_at_off_line_zero {s : ℝ} (hs : 0 < s)
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    originalSincMultiplier s (gammaOf (ρ : ℂ)) ≠ 0 := by
  rw [originalSincMultiplier_gammaOf]
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    have hre := ρ.2.2.1
    rw [h] at hre
    simp at hre
  have h1 : (ρ : ℂ) - 1 ≠ 0 := by
    intro h
    have hre := ρ.2.2.2
    rw [sub_eq_zero] at h
    rw [h] at hre
    simp at hre
  have him : (gammaOf (ρ : ℂ)).im ≠ 0 := by
    rw [Zeta23.WeilEF.gammaOf_im]
    exact sub_ne_zero.mpr (Ne.symm hoff)
  exact mul_ne_zero (mul_ne_zero h0 h1)
    (CCM.UniversalSinc.product_ne_zero_of_im_ne_zero hs him)

theorem originalSincMultiplier_I_half (s : ℝ) :
    originalSincMultiplier s (I / 2) = 0 := by
  norm_num [originalSincMultiplier, div_pow, I_sq]

theorem originalSincMultiplier_neg_I_half (s : ℝ) :
    originalSincMultiplier s (-I / 2) = 0 := by
  norm_num [originalSincMultiplier, div_pow, neg_sq, I_sq]

theorem hasDerivAt_originalSincMultiplier_I_half {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (originalSincMultiplier s)
      (-I * CCM.UniversalSinc.product s (I / 2)) (I / 2) := by
  have hP := (CCM.UniversalSinc.differentiable_product hs (I / 2)).hasDerivAt
  have hm := (((hasDerivAt_id (I / 2 : ℂ)).pow 2).add_const (1 / 4 : ℂ)).neg.mul hP
  change HasDerivAt (fun z : ℂ => -(z ^ 2 + 1 / 4) * CCM.UniversalSinc.product s z)
    (-I * CCM.UniversalSinc.product s (I / 2)) (I / 2)
  convert hm using 1 <;> norm_num [div_pow, I_sq] <;> ring

theorem hasDerivAt_originalSincMultiplier_neg_I_half {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (originalSincMultiplier s)
      (I * CCM.UniversalSinc.product s (-I / 2)) (-I / 2) := by
  have hP := (CCM.UniversalSinc.differentiable_product hs (-I / 2)).hasDerivAt
  have hm := (((hasDerivAt_id (-I / 2 : ℂ)).pow 2).add_const (1 / 4 : ℂ)).neg.mul hP
  change HasDerivAt (fun z : ℂ => -(z ^ 2 + 1 / 4) * CCM.UniversalSinc.product s z)
    (I * CCM.UniversalSinc.product s (-I / 2)) (-I / 2)
  convert hm using 1 <;> norm_num [div_pow, neg_sq, I_sq] <;> ring

/-- Both mandatory nonreal zeros have a nonzero complex derivative. -/
theorem originalSincMultiplier_deriv_ne_zero_at_elementary_pair {s : ℝ} (hs : 0 < s) :
    deriv (originalSincMultiplier s) (I / 2) ≠ 0 ∧
      deriv (originalSincMultiplier s) (-I / 2) ≠ 0 := by
  rw [(hasDerivAt_originalSincMultiplier_I_half hs.le).deriv,
    (hasDerivAt_originalSincMultiplier_neg_I_half hs.le).deriv]
  constructor
  · exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (CCM.UniversalSinc.product_ne_zero_of_im_ne_zero hs (by norm_num))
  · exact mul_ne_zero I_ne_zero
      (CCM.UniversalSinc.product_ne_zero_of_im_ne_zero hs (by norm_num))

/-- The pole-killing polynomial contributes exactly the mandatory pair of
nonreal zeros. This is a pointwise zero classification, not a multiplicity
or physical-transform assertion. -/
theorem originalSincMultiplier_eq_zero_iff_of_im_ne_zero {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : z.im ≠ 0) :
    originalSincMultiplier s z = 0 ↔ z = I / 2 ∨ z = -I / 2 := by
  have hprod := CCM.UniversalSinc.product_ne_zero_of_im_ne_zero hs hz
  have hpoly : z ^ 2 + 1 / 4 = (z - I / 2) * (z + I / 2) := by
    calc
      z ^ 2 + 1 / 4 = z ^ 2 - (I / 2) ^ 2 := by norm_num [div_pow, I_sq]
      _ = (z - I / 2) * (z + I / 2) := by ring
  simp only [originalSincMultiplier, mul_eq_zero, hprod, or_false,
    neg_eq_zero, hpoly, sub_eq_zero, add_eq_zero_iff_eq_neg, neg_div]

/-- The zero-side coefficient remains a complex square. Its nonvanishing
does not use or insert an absolute-square replacement. -/
theorem originalSincMultiplier_square_ne_zero_at_off_line_zero {s : ℝ} (hs : 0 < s)
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    originalSincMultiplier s (gammaOf (ρ : ℂ)) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (originalSincMultiplier_ne_zero_at_off_line_zero hs ρ hoff)

/-- The required original scale has no visibility or coefficient premise. -/
theorem fixed_originalSincMultiplier_square_ne_zero_at_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    originalSincMultiplier CCM.UniversalSinc.fixedScale (gammaOf (ρ : ℂ)) ^ 2 ≠ 0 :=
  originalSincMultiplier_square_ne_zero_at_off_line_zero CCM.UniversalSinc.fixedScale_pos ρ hoff

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.originalSincMultiplier_ne_zero_at_off_line_zero
#print axioms Zeta23.ExceptionalZero.originalSincMultiplier_eq_zero_iff_of_im_ne_zero
#print axioms Zeta23.ExceptionalZero.fixed_originalSincMultiplier_square_ne_zero_at_off_line_zero
#print axioms Zeta23.ExceptionalZero.originalSincMultiplier_deriv_ne_zero_at_elementary_pair
