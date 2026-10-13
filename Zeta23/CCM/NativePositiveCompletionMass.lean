import Zeta23.CCM.NativePositiveCompletionCells
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Analytic prerequisites of the direct native mass route

These are the actual logarithmic measure substitution, its integrability,
and a per-cell integral cap. The finite exact head formula and the complete
countable tail assembly remain separate obligations. No `605/621` theorem
or operator contraction is supplied by the file name or by the calibration.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

theorem nativePositiveCompletionLogDensity_integrableOn :
    IntegrableOn nativePositiveCompletionLogDensity (Ioi 1) := by
  have h := (integrableOn_comp_log_Ioi nativePositiveCompletion
    (a := (1 : ℝ)) (by norm_num)).mpr (by
      simpa only [Real.log_one] using nativePositiveCompletion_integrableOn)
  simpa only [nativePositiveCompletionLogDensity, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using h

theorem nativePositiveCompletion_mass_eq_logIntegral :
    (∫ t : ℝ in Ioi 0, nativePositiveCompletion t) =
      ∫ u : ℝ in Ioi 1, nativePositiveCompletionLogDensity u := by
  simpa only [nativePositiveCompletionLogDensity, smul_eq_mul,
    div_eq_mul_inv, mul_comm, Real.log_one] using
    (integral_comp_log_Ioi nativePositiveCompletion (a := (1 : ℝ)) (by norm_num)).symm

theorem nativePositiveCompletionLogDensity_cell_integral_le {n : ℕ} (hn : 0 < n) :
    (∫ u : ℝ in Ioo (n : ℝ) ((n : ℝ) + 1), nativePositiveCompletionLogDensity u) ≤
      (n : ℝ) ^ (-3 / 2 : ℝ) / 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hi : IntegrableOn nativePositiveCompletionLogDensity
      (Ioo (n : ℝ) ((n : ℝ) + 1)) :=
    nativePositiveCompletionLogDensity_integrableOn.mono_set (fun u hu => hn1.trans_lt hu.1)
  have hcont : Continuous (fun u : ℝ => (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) + 1 - u)) :=
    continuous_const.mul (continuous_const.sub continuous_id)
  have hcap : IntegrableOn
      (fun u : ℝ => (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) + 1 - u))
      (Ioo (n : ℝ) ((n : ℝ) + 1)) :=
    (hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hmono := setIntegral_mono_on hi hcap measurableSet_Ioo
    (fun u hu => nativePositiveCompletionLogDensity_cell_le hn hu.1.le hu.2)
  refine hmono.trans_eq ?_
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1),
    intervalIntegral.integral_const_mul]
  have hconst : IntervalIntegrable (fun _ : ℝ => (n : ℝ) + 1) volume
      (n : ℝ) ((n : ℝ) + 1) := continuous_const.intervalIntegrable _ _
  have hid : IntervalIntegrable (fun u : ℝ => u) volume
      (n : ℝ) ((n : ℝ) + 1) := continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_integrableOn
#print axioms Zeta23.CCM.nativePositiveCompletion_mass_eq_logIntegral
#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_cell_integral_le
