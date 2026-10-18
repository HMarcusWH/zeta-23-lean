import Zeta23.ExceptionalZero.UniversalSincPhysicalDetector
import Zeta23.ExceptionalZero.WeilZeroSideEvenization

/-!
# The actual fixed-source correlation is real

The actual zeta involution `rho -> 1-rho` preserves multiplicity and
reverses the centered spectral parameter. An even physical test therefore
has an even squared-filter family. Hermitian translation algebra then
proves realness, retaining the exact physical translation `t = 2a`.
The one-sub involution is the existing concrete-zeta construction from
conjugation and reflection, not an added abstract zero-model assumption.
-/

noncomputable section

open Complex
open scoped Topology ComplexConjugate

namespace Zeta23.ExceptionalZero

private theorem squaredWeilCoeff_oneSub {k : ℝ → ℂ} (hk : Function.Even k)
    (ρ : zetaZeroConfig.carrier) :
    zeroFilterCoeff (squaredWeilZeroFilter k) (zetaOneSubEquiv ρ) =
      zeroFilterCoeff (squaredWeilZeroFilter k) ρ := by
  rw [zeroFilterCoeff_squaredWeilZeroFilter, zeroFilterCoeff_squaredWeilZeroFilter,
    gammaOf_zetaOneSubEquiv, paperFT_neg_eq_paperFT_of_even hk]
  have hm : zeroMult (zetaOneSubEquiv ρ) = zeroMult ρ := zetaOneSubEquiv_mult ρ
  rw [hm]

theorem squaredWeilFilteredFamily_even {k : ℝ → ℂ} (hk : Function.Even k) :
    Function.Even (filteredZeroFamily (squaredWeilZeroFilter k) (1 / 2 : ℂ)) := by
  intro a
  unfold filteredZeroFamily
  calc
    _ = ∑' ρ : zetaZeroConfig.carrier,
        filteredZeroTerm (squaredWeilZeroFilter k) (1 / 2 : ℂ) (zetaOneSubEquiv ρ) a := by
      apply tsum_congr
      intro ρ
      unfold filteredZeroTerm
      rw [squaredWeilCoeff_oneSub hk]
      congr 1
      congr 1
      simp only [zetaOneSubEquiv_coe, Complex.ofReal_neg]
      ring
    _ = _ := Equiv.tsum_eq zetaOneSubEquiv
      (fun ρ : zetaZeroConfig.carrier =>
        filteredZeroTerm (squaredWeilZeroFilter k) (1 / 2 : ℂ) ρ a)

private theorem weilRelativeCorrelation_neg_eq_star
    (Z : ZeroConfig) (k : ℝ → ℂ) (t : ℝ) :
    weilRelativeCorrelation Z k (-t) =
      (starRingEnd ℂ) (weilRelativeCorrelation Z k t) := by
  have h := W_translateRight_both Z (translateRight k (-t)) k t
  have hdouble : translateRight (translateRight k (-t)) t = k := by
    funext x
    simp [translateRight]
  rw [hdouble] at h
  exact h.symm.trans (W_f_translateRight_eq_star_relativeCorrelation Z k t)

/-- Realness at the original aperture, with the complete complex-square
coefficient and factor-two translation convention. -/
theorem weilRelativeCorrelation_two_mul_im_eq_zero_of_real_even {k : ℝ → ℂ}
    (hreal : ∀ x : ℝ, (k x).im = 0) (hk : Function.Even k) (a : ℝ) :
    (weilRelativeCorrelation zetaZeroConfig k (2 * a)).im = 0 := by
  have heven : weilRelativeCorrelation zetaZeroConfig k (-(2 * a)) =
      weilRelativeCorrelation zetaZeroConfig k (2 * a) := by
    rw [show -(2 * a) = 2 * (-a) by ring,
      weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared hreal hk,
      weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared hreal hk]
    exact squaredWeilFilteredFamily_even hk a
  have hstar := (weilRelativeCorrelation_neg_eq_star zetaZeroConfig k (2 * a)).symm.trans heven
  have him := congrArg Complex.im hstar
  simp only [Complex.conj_im] at him
  linarith

theorem originalSincCorrelation_im_eq_zero {s : ℝ} (hs : 0 < s) (a : ℝ) :
    (weilRelativeCorrelation zetaZeroConfig (originalSincTest s) (2 * a)).im = 0 :=
  weilRelativeCorrelation_two_mul_im_eq_zero_of_real_even
    (originalSincTest_im_eq_zero hs) (originalSincTest_even hs) a

theorem fixed_originalSincCorrelation_im_eq_zero (a : ℝ) :
    (weilRelativeCorrelation zetaZeroConfig
      (originalSincTest CCM.UniversalSinc.fixedScale) (2 * a)).im = 0 :=
  originalSincCorrelation_im_eq_zero CCM.UniversalSinc.fixedScale_pos a

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.squaredWeilFilteredFamily_even
#print axioms Zeta23.ExceptionalZero.fixed_originalSincCorrelation_im_eq_zero
