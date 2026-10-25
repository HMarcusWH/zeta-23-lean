import Zeta23.OPICAFollowup.NearGapLimits

/- Explicit intended statements written from frozen paper CT1.3 before this
consumer's first elaboration. No reflected or copied inferred theorem types. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace OPICACT1SincBudgetIndependent
open Zeta23.OPICA Zeta23.OPICAFollowup

theorem expected_ct13_original_pairing {L : ℝ} (hL : 0 < L) (hlog : L < Real.log 2) :
    (nearGapCombFamily L).integral sincSquared =
      2 * (Real.exp L - 1) / (Real.exp L) ^ (3 / 2 : ℝ) ∧
    (nearGapCombFamily L).integral unitTriangle =
      2 * (Real.exp L - 1) / (Real.exp L) ^ (3 / 2 : ℝ) := by
  refine ⟨CT13Support.sinc_identity_original hL hlog, ?_⟩
  exact (signed_sinc_triangle_pairing _ (nearGapCombFamily_growth L)
    (nearGapCombFamily_fourier_selfdual L)).symm.trans (CT13Support.sinc_identity_original hL hlog)

theorem expected_ct13_jordan_masses {L : ℝ} (hL : 0 < L) (hlog : L < Real.log 2) :
    (∫ x, sincSquared x ∂(nearGapCombFamily L).negative) = 0 ∧
    (∫ x, sincSquared x ∂(nearGapCombFamily L).positive) =
      2 * (Real.exp L - 1) / (Real.exp L) ^ (3 / 2 : ℝ) := by
  refine ⟨CT13Support.negative_sinc_mass_zero hL, ?_⟩
  exact (CT13Support.positive_sinc_mass hL hlog).trans
    ((CT13Support.sinc_identity hL hlog).symm.trans (CT13Support.sinc_identity_original hL hlog))

theorem expected_ct13_first_order_cost :
    Tendsto (fun L : ℝ => (∫ x, sincSquared x ∂(nearGapCombFamily L).positive) / L)
      (𝓝[>] 0) (𝓝 2) :=
  CT13Support.positive_sinc_mass_slope

theorem expected_ct13_second_order_cost :
    Tendsto (fun L : ℝ => (∫ x, sincSquared x ∂(nearGapCombFamily L).positive) / L ^ 2)
      (𝓝[>] 0) atTop :=
  CT13Support.positive_sinc_mass_normalization_cost

/-- The family is outside the exact-unit-gap domain of the zero-jet span. -/
theorem expected_ct13_not_unit_gap {L : ℝ} (hL : 0 < L) (hlog : L < Real.log 2) :
    ¬(nearGapCombFamily L).HasUnitGap := by
  intro hgap
  have hx : ({Real.exp (-L)} : Set ℝ) ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    have heq : x = Real.exp (-L) := hx
    subst x
    exact ⟨by linarith [Real.exp_pos (-L)], (nearGapComb_radius_bounds hL hlog).2⟩
  have hz := measure_mono_null hx hgap.1
  have hm := (nearGapCombFamily_gap_edge_atom hL hlog).1
  change ((nearGapCombFamily L).positive {Real.exp (-L)}).toReal = _ at hm
  rw [hz, ENNReal.toReal_zero] at hm
  exact Real.exp_ne_zero _ hm.symm

end OPICACT1SincBudgetIndependent
#print axioms OPICACT1SincBudgetIndependent.expected_ct13_original_pairing
#print axioms OPICACT1SincBudgetIndependent.expected_ct13_jordan_masses
#print axioms OPICACT1SincBudgetIndependent.expected_ct13_first_order_cost
#print axioms OPICACT1SincBudgetIndependent.expected_ct13_second_order_cost
#print axioms OPICACT1SincBudgetIndependent.expected_ct13_not_unit_gap
