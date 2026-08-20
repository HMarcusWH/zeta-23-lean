import Zeta23.ExceptionalZero.FilteredZeroFamily

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set

/-- The absolute coefficient mass controls the complete filtered zero family by the crude strip
exponential `exp a` for every nonnegative aperture. -/
theorem norm_filteredZeroFamily_le_coeffMass_mul_exp
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2) {a : ℝ} (ha : 0 ≤ a) :
    ‖filteredZeroFamily φ c a‖ ≤
      (∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖) * Real.exp a := by
  have hcoeff : Summable (fun ρ : zetaZeroConfig.carrier => ‖zeroFilterCoeff φ ρ‖) := by
    simpa [AbsolutelySummableZeroFilter] using hφ
  have hmajor : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zeroFilterCoeff φ ρ‖ * Real.exp a) :=
    hcoeff.mul_right (Real.exp a)
  unfold filteredZeroFamily
  calc
    ‖∑' ρ : zetaZeroConfig.carrier, filteredZeroTerm φ c ρ a‖ ≤
        ∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖ * Real.exp a := by
      exact tsum_of_norm_bounded hmajor.hasSum (fun ρ => by
        unfold filteredZeroTerm
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_filteredZeroExp_le hc ρ ha) (norm_nonneg _))
    _ = (∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖) * Real.exp a :=
      hcoeff.tsum_mul_right (Real.exp a)

/-- For the filtered zero family, the eventual definition of subexponential growth can be upgraded
to one global exponential envelope on `[0,∞)`.  The finite prefix is controlled by the crude strip
bound above; the tail uses `Subexponential` directly. -/
theorem exists_global_exp_bound_of_subexponential_filteredZeroFamily
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (hsub : Subexponential (fun a => ‖filteredZeroFamily φ c a‖))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a →
      ‖filteredZeroFamily φ c a‖ ≤ C * Real.exp (ε * a) := by
  obtain ⟨A, hA⟩ := hsub ε hε
  let S : ℝ := ∑' ρ : zetaZeroConfig.carrier, ‖zeroFilterCoeff φ ρ‖
  let B : ℝ := max A 0
  let C : ℝ := 1 + S * Real.exp B
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun ρ => norm_nonneg _)
  have hC : 0 < C := by
    have hnonneg : 0 ≤ S * Real.exp B :=
      mul_nonneg hS (Real.exp_pos B).le
    dsimp [C]
    linarith
  have hCone : 1 ≤ C := by
    have hnonneg : 0 ≤ S * Real.exp B :=
      mul_nonneg hS (Real.exp_pos B).le
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro a ha
  by_cases htail : A ≤ a
  · calc
      ‖filteredZeroFamily φ c a‖ ≤ Real.exp (ε * a) := hA a htail
      _ = 1 * Real.exp (ε * a) := by ring
      _ ≤ C * Real.exp (ε * a) :=
        mul_le_mul_of_nonneg_right hCone (Real.exp_pos (ε * a)).le
  · have haA : a ≤ B := by
      dsimp [B]
      exact le_max_of_le_left (le_of_not_ge htail)
    have hcrude := norm_filteredZeroFamily_le_coeffMass_mul_exp hφ hc ha
    have hprefix : S * Real.exp a ≤ S * Real.exp B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr haA) hS
    have hone : 1 ≤ Real.exp (ε * a) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hε.le ha)
    calc
      ‖filteredZeroFamily φ c a‖ ≤ S * Real.exp a := by
        simpa [S] using hcrude
      _ ≤ S * Real.exp B := hprefix
      _ ≤ C := by
        dsimp [C]
        linarith
      _ = C * 1 := by ring
      _ ≤ C * Real.exp (ε * a) :=
        mul_le_mul_of_nonneg_left hone hC.le

end Zeta23.ExceptionalZero
