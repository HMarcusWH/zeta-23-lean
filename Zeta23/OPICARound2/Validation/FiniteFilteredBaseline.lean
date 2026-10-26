import Zeta23.OPICARound2.FiniteFilteredBaseline

/-! Independent consumers of the complete cell-series bound. The native
channel transport is deliberately not an input to these arithmetic checks. -/

noncomputable section

namespace Zeta23.OPICARound2.Validation

theorem baseline_series_strict_upper :
    (∑' n : ℕ, baselineSeriesTerm n) < (17 / 250 : ℝ) := by
  apply lt_of_le_of_lt baseline_series_abel_upper
  norm_num

theorem baseline_series_below_witness :
    (∑' n : ℕ, baselineSeriesTerm n) <
      (8192 / 93025 : ℝ) * (2096767 / 2097152 : ℝ) ^ 2 := by
  apply lt_of_lt_of_le baseline_series_strict_upper
  norm_num

/-- This consumer needs every tail length, not merely the enumerated prefix. -/
theorem baseline_all_prefixes_strict_upper (N : ℕ) :
    (∑ i ∈ Finset.range N, baselineSeriesTerm i) < (17 / 250 : ℝ) := by
  apply lt_of_le_of_lt (baselineSeries_partial_le N)
  rw [baseline_abel_budget_exact]
  norm_num

theorem baseline_literal_cell_controls_all (n : ℕ) :
    baselineCellResidual (n + 12) = baselinePeriod n := by
  rw [baseline_cell_periodic, baseline_cell_eq_period]

/-- An analytic consumer of the literal floor residual and the entire tail. -/
theorem baseline_physical_floor_energy_strict_upper :
    (∫ y : ℝ in Set.Ioi 1,
      (1 - (⌊y⌋₊ : ℝ) + (⌊y / 2⌋₊ : ℝ) + (⌊y / 3⌋₊ : ℝ) +
        (2 / 3 : ℝ) * (⌊y / 4⌋₊ : ℝ)) ^ 2 / y ^ 2) < (17 / 250 : ℝ) := by
  apply lt_of_le_of_lt baselineClassicalEnergy_integral_upper
  norm_num

/-- The exact original four-column fractional-part trial has the certified
classical energy upper, before transport into the native filtered channel. -/
theorem baseline_original_classical_four_column_strict_upper :
    (∫ x : ℝ in Set.Ioi 0,
      ‖classicalFiniteResidual (![1, -1, -1, -(2 / 3)] : Fin 4 → ℂ) x‖ ^ 2) <
        (17 / 250 : ℝ) := by
  have he : baselineComplexCoefficients = (![1, -1, -1, -(2 / 3)] : Fin 4 → ℂ) := by
    ext i
    fin_cases i <;> norm_num [baselineComplexCoefficients, baselineCoefficients]
  rw [← he]
  apply lt_of_le_of_lt baseline_classical_residual_integral_upper
  norm_num

#print axioms baseline_series_strict_upper
#print axioms baseline_series_below_witness
#print axioms baseline_all_prefixes_strict_upper
#print axioms baseline_physical_floor_energy_strict_upper
#print axioms baseline_original_classical_four_column_strict_upper


/-- The original rational coefficients are consumed in the unchanged native
filter, with the full analytic tail and the original source retained. -/
theorem baseline_actual_native_four_column_upper :
    ‖fixedFilteredProbeResidual (![1, -1, -1, -(2 / 3)] : Fin 4 → ℂ)‖ ^ 2 ≤
      (315384568453197375401 / 4648566756368995059600 : ℝ) := by
  have he : baselineComplexCoefficients = (![1, -1, -1, -(2 / 3)] : Fin 4 → ℂ) := by
    ext i
    fin_cases i <;> norm_num [baselineComplexCoefficients, baselineCoefficients]
  rw [← he]
  exact baseline_native_filtered_upper

theorem baseline_actual_zero_witness_lower (rho : zetaZeroConfig.carrier)
    (hr0 : (3 / 4 : ℝ) ≤ (rho : ℂ).re) (hr1 : (rho : ℂ).re ≤ 7 / 8)
    (hi0 : (1 : ℝ) ≤ |(rho : ℂ).im|) (hi1 : |(rho : ℂ).im| ≤ 2) :
    (4396431852289 / 49942416588800 : ℝ) ≤
      ‖fixedFilteredProbeResidual (![1, -1, -1, -(2 / 3)] : Fin 4 → ℂ)‖ ^ 2 :=
  filtered_rectangle_zero_witness_lower rho hr0 hr1 hi0 hi1 _

theorem baseline_actual_closed_rectangle_nonvanishing (z : ℂ)
    (hr0 : (3 / 4 : ℝ) ≤ z.re) (hr1 : z.re ≤ 7 / 8)
    (hi0 : (1 : ℝ) ≤ |z.im|) (hi1 : |z.im| ≤ 2) : riemannZeta z ≠ 0 :=
  filtered_baseline_rectangle_nonvanishing z hr0 hr1 hi0 hi1

theorem baseline_actual_reflected_rectangle_nonvanishing (z : ℂ)
    (hr0 : (1 / 8 : ℝ) ≤ z.re) (hr1 : z.re ≤ 1 / 4)
    (hi0 : (1 : ℝ) ≤ |z.im|) (hi1 : |z.im| ≤ 2) : riemannZeta z ≠ 0 :=
  filtered_baseline_reflected_rectangle_nonvanishing z hr0 hr1 hi0 hi1

#print axioms Zeta23.OPICARound2.filtered_four_column_region_certificate
#print axioms baseline_actual_native_four_column_upper
#print axioms baseline_actual_zero_witness_lower
#print axioms baseline_actual_closed_rectangle_nonvanishing
#print axioms baseline_actual_reflected_rectangle_nonvanishing

end Zeta23.OPICARound2.Validation
