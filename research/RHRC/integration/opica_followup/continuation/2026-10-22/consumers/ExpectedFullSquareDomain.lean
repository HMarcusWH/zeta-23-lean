import Zeta23.OPICAFollowup.SquareDefect

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace Zeta23.OPICAFollowup
open Zeta23.OPICA

theorem expected_original_distribution_tempered_domain {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (σ : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ)
    (hσ : σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ=0)
    (hT : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → T φ=σ.integral φ) :
    𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+T) ≠
      (squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+T :=
  square_actual_no_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne σ T hσ hT

theorem expected_existing_strong_domain_is_instance {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (σ : LocallyFiniteComplexMeasure) [σ.totalVariation.HasTemperateGrowth]
    (hσ : σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ=0) :
    𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+SquarePhysicalSupport.correctionDistribution σ) ≠
      (squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+SquarePhysicalSupport.correctionDistribution σ := by
  exact square_actual_no_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne σ (SquarePhysicalSupport.correctionDistribution σ)
    hσ (fun _ _ => rfl)

theorem expected_compact_extension_unique (σ : LocallyFiniteComplexMeasure)
    (T U : TemperedDistribution ℝ ℂ)
    (hT : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → T φ=σ.integral φ)
    (hU : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → U φ=σ.integral φ) : T=U :=
  TemperedLatticeBridge.extension_unique σ T U hT hU

theorem expected_full_domain_mixed_selfdual_barrier {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (S : TemperedDistribution ℝ ℂ) (hS : 𝓕 S=S)
    (σ : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ)
    (hσ : σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ=0)
    (hT : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → T φ=σ.integral φ) :
    𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+S+T) ≠
      (squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+S+T :=
  square_actual_no_selfdual_and_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne S hS σ T hσ hT

/-- Omitting compact compatibility would be mathematically false: a free
tempered distribution can cancel the square exactly. -/
theorem compact_compatibility_cannot_be_omitted (S : TemperedDistribution ℝ ℂ) :
    ∃ T : TemperedDistribution ℝ ℂ, 𝓕 (S+T)=S+T := by
  exact ⟨-S, by simp⟩

#print axioms Zeta23.OPICAFollowup.expected_original_distribution_tempered_domain
#print axioms Zeta23.OPICAFollowup.expected_existing_strong_domain_is_instance
#print axioms Zeta23.OPICAFollowup.expected_compact_extension_unique
#print axioms Zeta23.OPICAFollowup.expected_full_domain_mixed_selfdual_barrier
#print axioms Zeta23.OPICAFollowup.compact_compatibility_cannot_be_omitted
end Zeta23.OPICAFollowup
