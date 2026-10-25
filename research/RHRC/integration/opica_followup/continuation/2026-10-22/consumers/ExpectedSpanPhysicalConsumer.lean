import Zeta23.OPICAFollowup.Consumers
noncomputable section
open Set MeasureTheory Complex
open scoped SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

namespace IndependentSpanPhysicalConsumer
theorem expected_actual_zero_measure_span_consumer (data : List (ℂ × ℂ × ℕ))
    (h : ∀ j ∈ data, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
      j.2.2 < zeroJetOrder j.2.1) :
    (∀ j ∈ data, Continuous (zeroProfile j.2.1) ∧ Integrable (zeroProfile j.2.1) ∧
      MemLp (zeroProfile j.2.1) 2 ∧ 𝓕 (zeroProfile j.2.1) = zeroProfile j.2.1 ∧
      (j.2.2 = 0 → normalizedZeroMeasureJet j.2.1 j.2.2 = zeroMeasure j.2.1)) ∧
    (∃ hg : (Zeta23.OPICAFollowup.zeroJetRealSpan data).HasLinearGrowth,
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).FourierSelfdual hg ∧
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).HasUnitGap ∧
      ((Zeta23.OPICAFollowup.zeroJetRealSpan data).negative integerLatticeᶜ = 0 →
        (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
          (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0)) ∧
    (∀ n : ℕ, ∀ basis : Fin n → List (ℂ × ℂ × ℕ),
      ∀ hb : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      LinearIndependent ℝ (fun i =>
        (Zeta23.OPICAFollowup.zeroJetRealSpan (basis i)).distributionOfLinearGrowth
          (zeroJetRealSpan_growth _ (hb i))) →
      ∀ a : Fin n → ℝ,
      (Zeta23.OPICAFollowup.zeroJetRealSpan (realBasisCombinationData basis a)).negative
        integerLatticeᶜ = 0 → a = 0) :=
  Zeta23.OPICAFollowup.actual_zero_measure_span_consumer data h

#print axioms IndependentSpanPhysicalConsumer.expected_actual_zero_measure_span_consumer
end IndependentSpanPhysicalConsumer
