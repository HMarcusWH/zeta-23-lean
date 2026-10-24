import Zeta23.OPICAFollowup.MovingSourceWindowRate

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23 Zeta23.OPICAFollowup
namespace IndependentPhysicalWindowRates

theorem expected_fixed_source (d : ℕ) (C : ℝ) (C_gt_one : 1 < C) :
    Tendsto (fun T : ℝ =>
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily d t|^2))/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  native_fixed_source_window_rate d C C_gt_one

theorem expected_slow_source (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop)
    (order : ℕ → ℕ)
    (slow : Tendsto (fun n => (order n : ℝ)*Real.log ((order n : ℝ)+2)/time n) atTop (𝓝 0))
    (C : ℝ) (C_gt_one : 1 < C) :
    Tendsto (fun n =>
      Real.log (1+(∫ t : ℝ in Icc (time n-C*Real.log (time n)) (time n),
        |primeFieldFamily (order n) t|^2))/(2*time n)) atTop (𝓝 nativeZeroDisplacementSup) :=
  native_slow_source_window_rate time cofinal order slow C C_gt_one

theorem expected_order_zero (C : ℝ) (C_gt_one : 1 < C) :
    Tendsto (fun T : ℝ =>
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily 0 t|^2))/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  native_fixed_source_window_rate 0 C C_gt_one

theorem expected_nonpositive_finite_prefix :
    Tendsto (fun n : ℕ =>
      Real.log (1+(∫ t : ℝ in Icc (((n : ℝ)-5)-2*Real.log ((n : ℝ)-5)) ((n : ℝ)-5),
        |primeFieldFamily 0 t|^2))/(2*((n : ℝ)-5))) atTop (𝓝 nativeZeroDisplacementSup) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)-5) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-5 : ℝ) tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun n : ℕ => ((0 : ℕ) : ℝ)*Real.log (((0 : ℕ) : ℝ)+2)/((n : ℝ)-5))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact native_slow_source_window_rate (fun n => (n : ℝ)-5) ht (fun _ => 0) hs 2 (by norm_num)

theorem expected_both_source_factor_log_signs (rho : zetaZeroConfig.carrier)
    (right_zero : 1/2 < (rho : ℂ).re) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ d : ℕ,
      |Real.log ‖sourceFamilyLaplace d ((rho : ℂ)-1/2)‖| ≤ Cp*((d : ℝ)+1) :=
  NativeWindowProof.sourceFactor_abs_log_bound rho right_zero

theorem expected_literal_rate_definition (d : ℕ) (C T : ℝ) :
    nativeWindowLogRate d C T =
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily d t|^2))/(2*T) := rfl

theorem expected_zero_supremum_case (d : ℕ) (C : ℝ) (C_gt_one : 1 < C)
    (theta_zero : nativeZeroDisplacementSup=0) :
    Tendsto (fun T : ℝ =>
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily d t|^2))/(2*T))
      atTop (𝓝 0) := by
  simpa only [theta_zero] using native_fixed_source_window_rate d C C_gt_one

theorem zero_order_cost_correction_control :
    ¬ (∀ d : ℕ, ((d : ℝ)+1)*Real.log ((d : ℝ)+2) ≤
      2*((d : ℝ)*Real.log ((d : ℝ)+2))) := by
  intro h
  have hz := h 0
  norm_num at hz
  exact (not_le_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2))) hz

theorem upper_rate_does_not_force_zero_control {T : ℝ} (T_pos : 0 < T) :
    Real.log (1+(Real.exp (2*T)-1))/(2*T)=1 := by
  rw [show 1+(Real.exp (2*T)-1)=Real.exp (2*T) by ring,Real.log_exp]
  exact div_self (by positivity)

#print axioms Zeta23.OPICAFollowup.native_fixed_source_window_rate
#print axioms Zeta23.OPICAFollowup.native_slow_source_window_rate
#print axioms IndependentPhysicalWindowRates.expected_fixed_source
#print axioms IndependentPhysicalWindowRates.expected_slow_source
#print axioms IndependentPhysicalWindowRates.expected_order_zero
#print axioms IndependentPhysicalWindowRates.expected_nonpositive_finite_prefix
#print axioms IndependentPhysicalWindowRates.expected_both_source_factor_log_signs
#print axioms IndependentPhysicalWindowRates.expected_literal_rate_definition
#print axioms IndependentPhysicalWindowRates.expected_zero_supremum_case
#print axioms IndependentPhysicalWindowRates.zero_order_cost_correction_control
#print axioms IndependentPhysicalWindowRates.upper_rate_does_not_force_zero_control
end IndependentPhysicalWindowRates
