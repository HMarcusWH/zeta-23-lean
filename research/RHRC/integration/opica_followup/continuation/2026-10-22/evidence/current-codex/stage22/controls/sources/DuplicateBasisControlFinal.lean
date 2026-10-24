import Zeta23.OPICAFollowup.FiniteSpanSeparation
open Set MeasureTheory Complex
open scoped SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

namespace IndependentFiniteSpanFalsification

theorem repeated_actual_basis_is_not_independent (data : List JetDatum)
    (h : ∀ j ∈ data, ValidJet j) :
    ¬ LinearIndependent ℝ (fun _ : Fin 2 => (Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan data).distributionOfLinearGrowth
      (zeroJetRealSpan_growth data h)) := by
  intro hind
  have h01 : (0 : Fin 2) = 1 := hind.injective rfl
  norm_num at h01

theorem reflected_zero_is_the_same_jet (ρ : ℂ) (k : ℕ) :
    normalizedZeroMeasureJet (1-ρ) k = normalizedZeroMeasureJet ρ k :=
  normalizedZeroMeasureJet_one_sub ρ k

#print axioms IndependentFiniteSpanFalsification.repeated_actual_basis_is_not_independent
#print axioms IndependentFiniteSpanFalsification.reflected_zero_is_the_same_jet

end IndependentFiniteSpanFalsification
