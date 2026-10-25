import Zeta23.OPICAFollowup.FiniteSpanSeparation
open Set MeasureTheory Complex
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

-- Expected rejection1: missing physical off-lattice nonnegativity.
theorem negative_missing_off_lattice (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j) :
    (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0 := by
  exact Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero.1 data h

-- Expected rejection2: missing the actual multiplicity-bound domain.
theorem negative_missing_multiplicity (data : List JetDatum)
    (h : ∀ j ∈ data, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1)
    (hoff : (Zeta23.OPICAFollowup.zeroJetRealSpan data).OffLatticeNonnegative) :
    (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0 := by
  exact Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero.1 data h hoff

-- Expected rejection3: coefficient uniqueness requires an independent actual basis.
theorem negative_missing_independence {n : ℕ} (basis : Fin n → List JetDatum)
    (h : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : Fin n → ℝ)
    (hoff : (Zeta23.OPICAFollowup.zeroJetRealSpan (realBasisCombinationData basis a)).OffLatticeNonnegative) : a = 0 := by
  exact Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero.2 n basis h a hoff
