import Zeta23.OPICAFollowup.FiniteSpanSeparation
open MeasureTheory
open Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan
example {n : ℕ} (basis : Fin n → List JetDatum)
    (valid : ∀ i, ∀ j ∈ basis i, ValidJet j) :
    ∃ c : ℝ, 0<c := by
  exact ⟨(fixed_basis_negative_mass_budget basis valid).choose,
    (fixed_basis_negative_mass_budget basis valid).choose_spec.1⟩
