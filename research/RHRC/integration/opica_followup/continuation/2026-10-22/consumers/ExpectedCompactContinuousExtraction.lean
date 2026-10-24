import Zeta23.OPICAFollowup.NearGapLimits

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ENNReal FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.IndependentCompactExtractionConsumer
open Zeta23.OPICA

/- Literal actual-measure expected statement for the missing HT2 local
continuous-test topology. No assumed compact-test convergence is an input. -/
theorem expected_full_HT2_compact_continuous_extraction
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C*(1+R))
    (growth : ∀ n, (ν n).HasLinearGrowth)
    (selfdual : ∀ n, (ν n).FourierSelfdual (growth n))
    (positiveOff : ∀ n, (ν n).negative integerLatticeᶜ = 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n ∧ a n ≤ 1)
    (gap : ∀ n, (ν n).positive (Ioo (-a n) (a n)) = 0 ∧
      (ν n).negative (Ioo (-a n) (a n)) = 0)
    (sharp : Tendsto a atTop (𝓝 1)) :
    (∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => (∫ x, f x ∂(ν n).positive) - (∫ x, f x ∂(ν n).negative))
        atTop (𝓝 0)) ∧
    ∃ s : ℕ → ℕ, ∃ μ : LocallyFiniteSignedMeasure,
      StrictMono s ∧ μ.positive = 0 ∧ μ.negative = 0 ∧ μ.HasLinearGrowth ∧
      ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
        Tendsto (fun n => (∫ x, f x ∂(ν (s n)).positive) -
          (∫ x, f x ∂(ν (s n)).negative)) atTop
          (𝓝 ((∫ x, f x ∂μ.positive) - (∫ x, f x ∂μ.negative))) := by
  constructor
  · intro f continuous compact
    simpa only [IndependentCompactExtraction.extractedZeroMeasure, integral_zero_measure, sub_self] using
      IndependentCompactExtraction.expected_near_gap_compact_continuous_limit_zero
        ν C common growth selfdual positiveOff a ha gap sharp f continuous compact
  · exact IndependentCompactExtraction.expected_near_gap_genuine_zero_measure_extraction
      ν C common growth selfdual positiveOff a ha gap sharp

#print axioms Zeta23.OPICAFollowup.IndependentCompactExtractionConsumer.expected_full_HT2_compact_continuous_extraction
end Zeta23.OPICAFollowup.IndependentCompactExtractionConsumer
