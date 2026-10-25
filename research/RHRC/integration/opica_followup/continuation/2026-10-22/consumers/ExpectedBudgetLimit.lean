import Zeta23.OPICAFollowup.FiniteSpanSeparation

/-!
Post-green supporting consequence, outside the original primary-root inventory.

The basis is fixed and independent in the literal actual real zero-jet
distribution space. The negative mass is global off-lattice sinc-squared
mass of the canonical Jordan negative measure of the actual combination.
The only quantitative input is the original full fixed-basis budget.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup
open Zeta23.OPICAFollowup.FiniteSpan

namespace PostGreenFixedBasis

theorem coefficients_tendsto_zero_of_actual_negative_mass_tendsto_zero {n : ℕ}
    (basis : Fin n → List (ℂ × ℂ × ℕ))
    (valid : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧
      0 < j.2.1.re ∧ j.2.1.re < 1 ∧ j.2.2 < zeroJetOrder j.2.1)
    (independent : LinearIndependent ℝ (fun i =>
      (actualZeroJetSum (basis i)).rePart.distributionOfLinearGrowth
        (zeroJetRealSpan_growth (basis i) (valid i))))
    (a : ℕ → EuclideanSpace ℝ (Fin n))
    (hmass : Tendsto (fun k => ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,
      sincSquared x ∂(actualZeroJetSum ((List.ofFn (fun i =>
        (basis i).map (fun j => (((a k i : ℝ) : ℂ) * j.1, j.2.1, j.2.2)))).flatten)).rePart.negative)
      atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ :=
    Zeta23.OPICAFollowup.fixed_basis_negative_mass_budget basis valid independent
  have hdiv : Tendsto (fun k => (∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,
      sincSquared x ∂(actualZeroJetSum ((List.ofFn (fun i =>
        (basis i).map (fun j => (((a k i : ℝ) : ℂ) * j.1, j.2.1, j.2.2)))).flatten)).rePart.negative) / c)
      atTop (𝓝 0) := by
    simpa only [zero_div] using hmass.div_const c
  refine squeeze_zero_norm (fun k => ?_) hdiv
  apply (le_div_iff₀ hc).2
  have hb : c * ‖a k‖ ≤ ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,
      sincSquared x ∂(actualZeroJetSum ((List.ofFn (fun i =>
        (basis i).map (fun j => (((a k i : ℝ) : ℂ) * j.1, j.2.1, j.2.2)))).flatten)).rePart.negative := by
    simpa only [realBasisCombinationData, scaleJetData,
      Zeta23.OPICAFollowup.zeroJetRealSpan,
      Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan, integerLattice] using hbound (a k)
  simpa only [mul_comm] using hb

#print axioms PostGreenFixedBasis.coefficients_tendsto_zero_of_actual_negative_mass_tendsto_zero

end PostGreenFixedBasis

