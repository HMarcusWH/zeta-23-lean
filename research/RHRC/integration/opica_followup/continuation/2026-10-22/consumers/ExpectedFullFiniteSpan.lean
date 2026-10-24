import Zeta23.OPICAFollowup.FiniteSpanSeparation
noncomputable section
open Set MeasureTheory Complex
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

namespace IndependentFullFiniteSpan
theorem full_original_domain_and_independent_basis :
    (∀ data : List (ℂ × ℂ × ℕ),
      ∀ h : ∀ j ∈ data, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative integerLatticeᶜ = 0 →
        (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
          (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0) ∧
    (∀ n : ℕ, ∀ basis : Fin n → List (ℂ × ℂ × ℕ),
      ∀ h : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      LinearIndependent ℝ (fun i =>
        (Zeta23.OPICAFollowup.zeroJetRealSpan (basis i)).distributionOfLinearGrowth
          (zeroJetRealSpan_growth _ (h i))) →
      ∀ a : Fin n → ℝ,
      (Zeta23.OPICAFollowup.zeroJetRealSpan (realBasisCombinationData basis a)).negative
        integerLatticeᶜ = 0 → a = 0) :=
  Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero

#print axioms IndependentFullFiniteSpan.full_original_domain_and_independent_basis
end IndependentFullFiniteSpan
