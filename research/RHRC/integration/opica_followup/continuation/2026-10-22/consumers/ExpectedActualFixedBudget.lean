import Zeta23.OPICAFollowup.FiniteSpanSeparation

noncomputable section
open Set MeasureTheory
open scoped Topology
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup
open Zeta23.OPICAFollowup.FiniteSpan
namespace IndependentActualFixedBudget

/-- Independent inline consumer expands the coefficient construction to
literal actual normalized zero-jet data and the norm to sqrt(sum squares). -/
theorem expected_full_actual_euclidean_budget {n : ℕ}
    (basis : Fin n → List (ℂ × ℂ × ℕ))
    (valid : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1=0 ∧
      0<j.2.1.re ∧ j.2.1.re<1 ∧ j.2.2<zeroJetOrder j.2.1)
    (independent : LinearIndependent ℝ (fun i =>
      (actualZeroJetSum (basis i)).rePart.distributionOfLinearGrowth
        (zeroJetRealSpan_growth (basis i) (valid i)))) :
    ∃ c_basis : ℝ, 0<c_basis ∧ ∀ a : Fin n → ℝ,
      c_basis*Real.sqrt (∑ i,‖a i‖^2) ≤
        ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,sincSquared x
          ∂(actualZeroJetSum ((List.ofFn (fun i =>
            (basis i).map (fun j => ((a i : ℂ)*j.1,j.2.1,j.2.2)))).flatten)).rePart.negative := by
  obtain ⟨c,hc,hbound⟩ := fixed_basis_negative_mass_budget basis valid independent
  refine ⟨c,hc,fun a => ?_⟩
  simpa only [EuclideanSpace.norm_eq,realBasisCombinationData,scaleJetData,Zeta23.OPICAFollowup.zeroJetRealSpan,
    Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan,integerLattice] using hbound (WithLp.toLp 2 a)

theorem no_positive_budget_without_independence :
    ¬ ∃ c : ℝ, 0<c ∧ ∀ a : EuclideanSpace ℝ (Fin 1),
      c*‖a‖ ≤ ∫ x in integerLatticeᶜ,sincSquared x
        ∂(Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan (realBasisCombinationData (fun _ : Fin 1 => []) (fun i => a i))).negative := by
  rintro ⟨c,hc,hbound⟩
  have h := hbound (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  simp [realBasisCombinationData,scaleJetData,Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan,actualZeroJetSum,
    zeroComplex,zeroJordan] at h
  linarith

#print axioms IndependentActualFixedBudget.expected_full_actual_euclidean_budget
#print axioms IndependentActualFixedBudget.no_positive_budget_without_independence
end IndependentActualFixedBudget
