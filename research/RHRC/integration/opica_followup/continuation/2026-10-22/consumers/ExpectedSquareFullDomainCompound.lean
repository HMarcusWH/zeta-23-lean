import Zeta23.OPICAFollowup.SquareDefect

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap

namespace Zeta23.OPICAFollowup.Validation

/-! This compound preserves both existing interfaces as genuine conjuncts.
Authored by the contract reviewer as an implementation leaf at the owner's
explicit request; its independent semantic review must come from the owner or
another nonauthor. It is not a new primary root or an approval artifact. -/

theorem expected_square_original_and_full_distribution_domain
    {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    (¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧
      ∀ φ : 𝓢(ℝ, ℂ),
        squareGapMeasure h A (𝓕 φ) + latticePairing c (𝓕 φ) =
          squareGapMeasure h A φ + latticePairing c φ) ∧
    (∀ (σ : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ),
      σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0 →
      (∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) →
        T φ = σ.integral φ) →
      𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
          (squareGapJordan_growth hcont hvan A) + T) ≠
        (squareGapJordan h A hcont).distributionOfLinearGrowth
          (squareGapJordan_growth hcont hvan A) + T) := by
  refine ⟨square_no_lattice_repair hev hcont hint hL2 hsd hvan hpl hne, ?_⟩
  intro σ T hσ hT
  exact square_actual_no_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne σ T hσ hT

#print axioms Zeta23.OPICAFollowup.Validation.expected_square_original_and_full_distribution_domain

end Zeta23.OPICAFollowup.Validation
