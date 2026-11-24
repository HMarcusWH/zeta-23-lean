import Zeta23.OPICASupport.OPICAStep4.BoundaryFlatCharacterization

/-!
Exact zero-sampling geometry on the unchanged native boundary-flat carrier.
The positive decomposition assumes the native C1 contract. No theorem in this
module supplies C1, RH, or injectivity of the zero-sampling map.
-/

noncomputable section

open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound4.ArithmeticFrontier

namespace Zeta23.OPICARound20

/-- A genuine zeta-zero sample, weighted by its actual positive multiplicity. -/
def zeroSampleEnergy (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult (ρ : ℂ) : ℝ) * Complex.normSq (paperFT f (gammaOf (ρ : ℂ)))

theorem zeroSampleEnergy_nonnegative (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier) :
    0 ≤ zeroSampleEnergy f ρ :=
  mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem zeta_Wsummand_re_eq_zeroSampleEnergy_of_re_eq_half
    (f : ℝ → ℂ) (ρ : zetaZeroConfig.carrier)
    (hρ : (ρ : ℂ).re = 1 / 2) :
    (zetaZeroConfig.Wsummand f f ρ).re = zeroSampleEnergy f ρ := by
  have hγ : (starRingEnd ℂ) (gammaOf (ρ : ℂ)) = gammaOf (ρ : ℂ) :=
    gammaOf_star_eq_self_of_criticalLine ρ hρ
  unfold ZeroConfig.Wsummand zeroSampleEnergy
  rw [hγ, mul_assoc, Complex.mul_conj]
  simp

theorem zeroSampleEnergy_summable_of_criticalLine
    (hline : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Summable (zeroSampleEnergy f) := by
  have hs := zeta_Wsummand_summable hf hf.continuous hfc hfc
  exact (Complex.hasSum_re hs.hasSum).summable.congr fun ρ =>
    zeta_Wsummand_re_eq_zeroSampleEnergy_of_re_eq_half f ρ (hline ρ ρ.property)

/-- Exact diagonal Gram identity. It sums over distinct actual zeta zeros;
multiplicity remains an explicit positive weight. -/
theorem zeta_W_re_eq_tsum_zeroSampleEnergy_of_criticalLine
    (hline : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (zetaZeroConfig.W f f).re = ∑' ρ, zeroSampleEnergy f ρ := by
  have hs := zeta_Wsummand_summable hf hf.continuous hfc hfc
  unfold ZeroConfig.W
  rw [Complex.re_tsum hs]
  exact tsum_congr fun ρ =>
    zeta_Wsummand_re_eq_zeroSampleEnergy_of_re_eq_half f ρ (hline ρ ρ.property)

/-- The full boundary-flat form is the exact weighted sample energy under C1.
No parity, pole-neutrality, or moment-slice condition is added. -/
theorem canonicalSourceEnergy_eq_zeroSampleEnergy_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u) :
    (quadraticForm (canonicalSourceMatrix L K) u).re =
      ∑' ρ, zeroSampleEnergy (localizedFiniteVector L K u) ρ := by
  rw [← zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm K u hL hflat]
  exact zeta_W_re_eq_tsum_zeroSampleEnergy_of_criticalLine
    (fun ρ hρ => RH_implies_on_line
      (riemannHypothesis_of_cofinal_moment_slice_bounds hC1) hρ)
    (contDiff_localizedFiniteVector_of_boundaryFlat K u hL hflat)
    (localizedFiniteVector_hasCompactSupport L K u)

/-- Every one actual-zero sample is a quantitative lower bound on the complete
legal finite source energy, conditional on C1. -/
theorem zeroSampleEnergy_le_canonicalSourceEnergy_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u) (ρ : zetaZeroConfig.carrier) :
    zeroSampleEnergy (localizedFiniteVector L K u) ρ ≤
      (quadraticForm (canonicalSourceMatrix L K) u).re := by
  rw [canonicalSourceEnergy_eq_zeroSampleEnergy_of_c1 hC1 hL K u hflat]
  have hs := zeroSampleEnergy_summable_of_criticalLine
    (fun ρ hρ => RH_implies_on_line
      (riemannHypothesis_of_cofinal_moment_slice_bounds hC1) hρ)
    (contDiff_localizedFiniteVector_of_boundaryFlat K u hL hflat)
    (localizedFiniteVector_hasCompactSupport L K u)
  exact hs.le_tsum ρ fun σ _ => zeroSampleEnergy_nonnegative _ σ

/-- Vanishing at every actual zero annihilates the complex finite Weil form.
This direction is unconditional; it does not require critical-line positivity. -/
theorem canonicalSourceQuadraticForm_zero_of_all_samples_zero
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u)
    (hzero : ∀ ρ : zetaZeroConfig.carrier,
      paperFT (localizedFiniteVector L K u) (gammaOf (ρ : ℂ)) = 0) :
    quadraticForm (canonicalSourceMatrix L K) u = 0 := by
  rw [← zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm K u hL hflat]
  unfold ZeroConfig.W
  simp only [ZeroConfig.Wsummand, hzero, mul_zero, zero_mul, tsum_zero]

/-- Under C1, a legal vector has zero source energy exactly when its transform
vanishes at every actual zeta zero. Sampling injectivity is a separate premise. -/
theorem canonicalSourceEnergy_zero_iff_all_samples_zero_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u) :
    (quadraticForm (canonicalSourceMatrix L K) u).re = 0 ↔
      ∀ ρ : zetaZeroConfig.carrier,
        paperFT (localizedFiniteVector L K u) (gammaOf (ρ : ℂ)) = 0 := by
  constructor
  · intro hzero ρ
    have hle := zeroSampleEnergy_le_canonicalSourceEnergy_of_c1 hC1 hL K u hflat ρ
    rw [hzero] at hle
    have hE : zeroSampleEnergy (localizedFiniteVector L K u) ρ = 0 :=
      le_antisymm hle (zeroSampleEnergy_nonnegative _ ρ)
    have hmNat : 0 < zetaZeroConfig.mult (ρ : ℂ) :=
      lt_of_lt_of_le Nat.zero_lt_one (zetaZeroConfig.one_le_mult ρ ρ.property)
    have hm : (0 : ℝ) < (zetaZeroConfig.mult (ρ : ℂ) : ℝ) := by exact_mod_cast hmNat
    unfold zeroSampleEnergy at hE
    exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hE).resolve_left (ne_of_gt hm))
  · intro hzero
    rw [canonicalSourceQuadraticForm_zero_of_all_samples_zero hL K u hflat hzero]
    rfl

/-- Strict positivity has one precise remaining obstruction: all zero samples
could vanish. This theorem makes no injectivity claim. -/
theorem canonicalSourceEnergy_pos_iff_exists_nonzero_sample_of_c1
    (hC1 : CofinalMomentSliceVanishingErrorBounds)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (hflat : BoundaryFlatCoefficients K u) :
    0 < (quadraticForm (canonicalSourceMatrix L K) u).re ↔
      ∃ ρ : zetaZeroConfig.carrier,
        paperFT (localizedFiniteVector L K u) (gammaOf (ρ : ℂ)) ≠ 0 := by
  constructor
  · intro hpos
    by_contra h
    push Not at h
    have hz := (canonicalSourceEnergy_zero_iff_all_samples_zero_of_c1 hC1 hL K u hflat).mpr h
    linarith
  · rintro ⟨ρ, hρ⟩
    have hmNat : 0 < zetaZeroConfig.mult (ρ : ℂ) :=
      lt_of_lt_of_le Nat.zero_lt_one (zetaZeroConfig.one_le_mult ρ ρ.property)
    have hm : (0 : ℝ) < (zetaZeroConfig.mult (ρ : ℂ) : ℝ) := by exact_mod_cast hmNat
    have hE : 0 < zeroSampleEnergy (localizedFiniteVector L K u) ρ :=
      mul_pos hm (Complex.normSq_pos.mpr hρ)
    exact hE.trans_le (zeroSampleEnergy_le_canonicalSourceEnergy_of_c1 hC1 hL K u hflat ρ)

end Zeta23.OPICARound20

set_option pp.fullNames true
set_option pp.universes false
set_option pp.maxSteps 100000

#check @Zeta23.OPICARound20.zeroSampleEnergy_nonnegative
#print axioms Zeta23.OPICARound20.zeroSampleEnergy_nonnegative
#check @Zeta23.OPICARound20.zeta_Wsummand_re_eq_zeroSampleEnergy_of_re_eq_half
#print axioms Zeta23.OPICARound20.zeta_Wsummand_re_eq_zeroSampleEnergy_of_re_eq_half
#check @Zeta23.OPICARound20.zeroSampleEnergy_summable_of_criticalLine
#print axioms Zeta23.OPICARound20.zeroSampleEnergy_summable_of_criticalLine
#check @Zeta23.OPICARound20.zeta_W_re_eq_tsum_zeroSampleEnergy_of_criticalLine
#print axioms Zeta23.OPICARound20.zeta_W_re_eq_tsum_zeroSampleEnergy_of_criticalLine
#check @Zeta23.OPICARound20.canonicalSourceEnergy_eq_zeroSampleEnergy_of_c1
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_eq_zeroSampleEnergy_of_c1
#check @Zeta23.OPICARound20.zeroSampleEnergy_le_canonicalSourceEnergy_of_c1
#print axioms Zeta23.OPICARound20.zeroSampleEnergy_le_canonicalSourceEnergy_of_c1
#check @Zeta23.OPICARound20.canonicalSourceQuadraticForm_zero_of_all_samples_zero
#print axioms Zeta23.OPICARound20.canonicalSourceQuadraticForm_zero_of_all_samples_zero
#check @Zeta23.OPICARound20.canonicalSourceEnergy_zero_iff_all_samples_zero_of_c1
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_zero_iff_all_samples_zero_of_c1
#check @Zeta23.OPICARound20.canonicalSourceEnergy_pos_iff_exists_nonzero_sample_of_c1
#print axioms Zeta23.OPICARound20.canonicalSourceEnergy_pos_iff_exists_nonzero_sample_of_c1
