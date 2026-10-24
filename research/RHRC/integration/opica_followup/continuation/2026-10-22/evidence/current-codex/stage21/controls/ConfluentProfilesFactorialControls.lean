import Zeta23.OPICAFollowup.ConfluentProfiles

noncomputable section
open Polynomial
namespace Zeta23.OPICAFollowup.OPICARightCellTaylor

theorem second_parameter_jet_cubic_coefficient :
    oddJetCoefficient (1 / 4) 2 1 = (-1 / 6 : ℂ) := by
  unfold oddJetCoefficient
  rw [← actual_polynomial_row]
  have hp : (X * (C (1 / 4 : ℂ) - X) ^ 1) =
      monomial 1 (1 / 4 : ℂ) - monomial 2 (1 : ℂ) := by
    simp only [← C_mul_X_pow_eq_monomial, pow_one, map_one, one_mul]
    ring
  rw [hp, map_sub]
  norm_num [Polynomial.hasseDeriv_monomial]

theorem missing_parameter_factorial_is_false :
    oddJetCoefficient (1 / 4) 2 1 ≠ (-1 / 3 : ℂ) := by
  rw [second_parameter_jet_cubic_coefficient]
  norm_num

/-- The zero-node hypothesis is indispensable even for the actual kernel. -/
theorem zero_node_actual_rightCell (u : ℝ) : rightCellJet 0 0 u = 0 := by
  simp [rightCellJet]

theorem zero_node_actual_dependency (u : ℝ) :
    (∑ i : Fin 1, (1 : ℂ) * rightCellJet 0 0 u) = 0 := by
  simp [zero_node_actual_rightCell]

theorem zero_node_coefficient_nonzero : (fun _ : Fin 1 => (1 : ℂ)) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num at hh

#print axioms Zeta23.OPICAFollowup.OPICARightCellTaylor.second_parameter_jet_cubic_coefficient
#print axioms Zeta23.OPICAFollowup.OPICARightCellTaylor.missing_parameter_factorial_is_false
#print axioms Zeta23.OPICAFollowup.OPICARightCellTaylor.zero_node_actual_dependency
end Zeta23.OPICAFollowup.OPICARightCellTaylor

