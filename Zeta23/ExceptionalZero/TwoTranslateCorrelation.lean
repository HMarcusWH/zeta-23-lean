import Zeta23.ExceptionalZero.TwoTranslateWeil
import Zeta23.ExceptionalZero.WeilFilter
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

/-!
# X2: two-translate correlation as a squared filtered-zero family

X0 fixed the exact Hermitian/conjugation convention for `ZeroConfig.W`.  X2 now identifies the
relative correlation of a real-even test with the generic R001 filtered exponential family whose
filter is the *square* of the natural Weil filter.

Claim-bearing normalizations:
* the relative translation is `2 * a`;
* the center is exactly `1 / 2`;
* the filter is `paperFT k (gammaOf ρ) ^ 2`, not a modulus square;
* multiplicity is inserted exactly once by `zeroFilterCoeff`.

No positivity, off-line-zero, determinant, or RH claim is made in this file.
-/

/-- The R001 filter produced by the complete two-translate correlation.  Multiplicity is deliberately
not part of this definition; `zeroFilterCoeff` inserts it exactly once. -/
def squaredWeilZeroFilter (k : ℝ → ℂ) : ZeroFilter :=
  fun ρ => (weilZeroFilter k ρ) ^ 2

/-- Multiplicity bookkeeping for the squared Weil filter. -/
theorem zeroFilterCoeff_squaredWeilZeroFilter (k : ℝ → ℂ)
    (ρ : zetaZeroConfig.carrier) :
    zeroFilterCoeff (squaredWeilZeroFilter k) ρ =
      (zeroMult (ρ : ℂ) : ℂ) * (paperFT k (gammaOf (ρ : ℂ))) ^ 2 := rfl

/-- For a pointwise real test, conjugating the transform at the conjugated spectral point reverses
the Fourier argument.  This is the first half of the real-even symmetry audit. -/
theorem star_paperFT_star_eq_paperFT_neg_of_real {k : ℝ → ℂ}
    (hreal : ∀ x : ℝ, (k x).im = 0) (z : ℂ) :
    (starRingEnd ℂ) (paperFT k ((starRingEnd ℂ) z)) = paperFT k (-z) := by
  unfold paperFT
  change conj (∫ u : ℝ, k u * Complex.exp (I * conj z * (u : ℂ))) =
    ∫ u : ℝ, k u * Complex.exp (I * (-z) * (u : ℂ))
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  have hk : conj (k u) = k u := by
    apply Complex.ext
    · simp
    · simp [hreal u]
  rw [map_mul, hk, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- Evenness removes the remaining sign in the paper Fourier convention. -/
theorem paperFT_neg_eq_paperFT_of_even {k : ℝ → ℂ}
    (heven : Function.Even k) (z : ℂ) :
    paperFT k (-z) = paperFT k z := by
  unfold paperFT
  let g : ℝ → ℂ := fun u => k u * Complex.exp (I * z * (u : ℂ))
  calc
    (∫ u : ℝ, k u * Complex.exp (I * (-z) * (u : ℂ))) =
        ∫ u : ℝ, g (-u) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [← heven u]
      simp only [g]
      congr 1
      push_cast
      ring
    _ = ∫ u : ℝ, g u := by
      simpa using (Measure.integral_comp_mul_left g (-1 : ℝ))

/-- **X2 Fourier-symmetry gate.**  For a real-even test, the second Fourier factor in the genuine
Weil summand is the same Fourier value as the first one. -/
theorem star_paperFT_star_eq_paperFT_of_real_even {k : ℝ → ℂ}
    (hreal : ∀ x : ℝ, (k x).im = 0) (heven : Function.Even k) (z : ℂ) :
    (starRingEnd ℂ) (paperFT k ((starRingEnd ℂ) z)) = paperFT k z := by
  rw [star_paperFT_star_eq_paperFT_neg_of_real hreal z,
    paperFT_neg_eq_paperFT_of_even heven z]

/-- **X2 legality gate.**  The squared natural Weil filter is absolutely summable under exactly the
usual `C²` compact-support hypotheses.  No new zero-counting estimate is used: the ordinary
multiplicity-weighted norm series is summable, its product with itself is summable, and the diagonal
majorizes the squared-filter coefficient because every zero multiplicity is at least one. -/
theorem absolutelySummableZeroFilter_squaredWeil {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    AbsolutelySummableZeroFilter (squaredWeilZeroFilter k) := by
  classical
  have hb0 := absolutelySummableZeroFilter_weil hk hkc
  unfold AbsolutelySummableZeroFilter at hb0 ⊢
  let b : zetaZeroConfig.carrier → ℝ :=
    fun ρ => ‖zeroFilterCoeff (weilZeroFilter k) ρ‖
  have hb : Summable b := by
    simpa [b] using hb0
  let B : ℝ := ∑' ρ : zetaZeroConfig.carrier, b ρ
  have hb_le_B : ∀ ρ : zetaZeroConfig.carrier, b ρ ≤ B := by
    intro ρ
    have hsingle := hb.sum_le_tsum {ρ} (fun σ _ => norm_nonneg _)
    simpa [B] using hsingle
  have hmajor : Summable (fun ρ : zetaZeroConfig.carrier => B * b ρ) :=
    hb.mul_left B
  refine hmajor.of_nonneg_of_le (fun ρ => norm_nonneg _) ?_
  intro ρ
  have hmNat : 1 ≤ zeroMult (ρ : ℂ) :=
    zetaZeroConfig.one_le_mult (ρ : ℂ) ρ.2
  have hmR : (1 : ℝ) ≤ (zeroMult (ρ : ℂ) : ℝ) := by
    exact_mod_cast hmNat
  have hm : (1 : ℝ) ≤ ‖((zeroMult (ρ : ℂ) : ℂ))‖ := by
    simpa using hmR
  have ha : 0 ≤ ‖paperFT k (gammaOf (ρ : ℂ))‖ := norm_nonneg _
  have hbound := hb_le_B ρ
  simp only [b, zeroFilterCoeff, squaredWeilZeroFilter, weilZeroFilter,
    norm_mul, norm_pow] at hbound ⊢
  nlinarith

/-- **X2 endpoint.**  For every real-even test and every real aperture, the complete relative Weil
correlation at translation `2a` is literally the generic R001 filtered exponential family of the
squared Weil filter at center `1/2`.

This is an exact identity in the repository's live Fourier convention: no modulus-square,
conjugation residue, second zero model, or normalization slack remains. -/
theorem weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared
    {k : ℝ → ℂ} (hreal : ∀ x : ℝ, (k x).im = 0) (heven : Function.Even k) (a : ℝ) :
    weilRelativeCorrelation zetaZeroConfig k (2 * a) =
      filteredZeroFamily (squaredWeilZeroFilter k) (1 / 2 : ℂ) a := by
  unfold weilRelativeCorrelation ZeroConfig.W filteredZeroFamily
  refine tsum_congr fun ρ => ?_
  unfold ZeroConfig.Wsummand filteredZeroTerm
  rw [paperFT_translateRight_gammaOf k a (ρ : ℂ)]
  rw [star_paperFT_star_eq_paperFT_of_real_even hreal heven]
  simp only [zeroFilterCoeff, squaredWeilZeroFilter, weilZeroFilter]
  simp only [zetaZeroConfig]
  ring

#print axioms Zeta23.ExceptionalZero.star_paperFT_star_eq_paperFT_of_real_even
#print axioms Zeta23.ExceptionalZero.absolutelySummableZeroFilter_squaredWeil
#print axioms Zeta23.ExceptionalZero.weilRelativeCorrelation_two_mul_eq_filteredZeroFamily_squared

end Zeta23.ExceptionalZero
