import Zeta23.CCM.OriginalSincLogDrive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Actual continuum cancellation in the original integer drive

The exponential substitution is justified on the genuine compact summand.
The continuum term equals exp(t/2) times the ordinary and first weighted
elementary source moments, and hence vanishes. Abel discrepancy then bounds
the actual U by the integral of its actual summand derivative. Exponential
decay of that derivative integral and stable Y membership remain separate.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Zeta23.CCM

private theorem actual_source_compact : HasCompactSupport nativeOriginalSource := by
  apply HasCompactSupport.intro (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale)
    isCompact_Icc
  exact fun x hx => nativeOriginalSource_supported x hx

private theorem exp_div_sqrt_exp (y : ℝ) :
    Real.exp y / Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have hsplit : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hroot : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
    rw [hsplit, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [hroot, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

private theorem actual_exp_summand (t y : ℝ) :
    Real.exp y * nativeOriginalLogDriveSummand t (Real.exp y) =
      y * Real.exp (y / 2) * nativeOriginalSource (t - y) := by
  simp only [nativeOriginalLogDriveSummand, if_pos (Real.exp_pos y), Real.log_exp]
  calc
    _ = y * (Real.exp y / Real.sqrt (Real.exp y)) * nativeOriginalSource (t - y) := by ring
    _ = _ := by rw [exp_div_sqrt_exp]

/-- Exact exponential substitution, with the zero neighborhood at the lower
endpoint proved from the actual compact source. -/
theorem nativeOriginalLogDriveSummand_integral_eq_exponential (t : ℝ) :
    (∫ x : ℝ, nativeOriginalLogDriveSummand t x) =
      ∫ y : ℝ, y * Real.exp (y / 2) * nativeOriginalSource (t - y) := by
  let a : ℝ := t - UniversalSinc.fixedScale - 1
  let F : ℝ → ℝ := nativeOriginalLogDriveSummand t
  let H : ℝ → ℝ := fun y => Real.exp y * F (Real.exp y)
  have hF : (∫ x : ℝ in Ioi (Real.exp a), F x) = ∫ x : ℝ, F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply nativeOriginalLogDriveSummand_zero_below
    have hxle : x ≤ Real.exp a := le_of_not_gt hx
    exact hxle.trans_lt (Real.exp_lt_exp.mpr (by dsimp [a]; linarith))
  have hH : (∫ y : ℝ in Ioi a, H y) = ∫ y : ℝ, H y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyle : y ≤ a := le_of_not_gt hy
    have hzero : F (Real.exp y) = 0 := by
      apply nativeOriginalLogDriveSummand_zero_below
      apply Real.exp_lt_exp.mpr
      dsimp [a] at hyle
      linarith
    dsimp only [H]
    rw [hzero, mul_zero]
  have hsub := integral_comp_exp_Ioi F a
  change (∫ y : ℝ in Ioi a, H y) = ∫ x : ℝ in Ioi (Real.exp a), F x at hsub
  rw [hF, hH] at hsub
  rw [← hsub]
  apply integral_congr_ae
  filter_upwards with y
  exact actual_exp_summand t y

/-- Both actual pole moments are needed: the first weighted moment cancels
the logarithmic coefficient that remains after the ordinary moment. -/
theorem nativeOriginalLogDriveSummand_integral_zero (t : ℝ) :
    (∫ x : ℝ, nativeOriginalLogDriveSummand t x) = 0 := by
  rw [nativeOriginalLogDriveSummand_integral_eq_exponential]
  let H : ℝ → ℝ := fun y => y * Real.exp (y / 2) * nativeOriginalSource (t - y)
  have hchange : (∫ y : ℝ, H y) = ∫ u : ℝ, H (t - u) :=
    (integral_sub_left_eq_self H volume t).symm
  change (∫ y : ℝ, H y) = 0
  rw [hchange]
  have heq : (fun u : ℝ => H (t - u)) = fun u =>
      Real.exp (t / 2) * (t * (Real.exp (-u / 2) * nativeOriginalSource u) -
        u * Real.exp (-u / 2) * nativeOriginalSource u) := by
    funext u
    dsimp only [H]
    rw [sub_sub_cancel, show (t - u) / 2 = t / 2 + (-u / 2) by ring, Real.exp_add]
    ring
  have hE : Continuous (fun u : ℝ => Real.exp (-u / 2)) := by fun_prop
  have h0int : Integrable (fun u : ℝ => Real.exp (-u / 2) * nativeOriginalSource u) :=
    (hE.mul nativeOriginalSource_contDiff.continuous).integrable_of_hasCompactSupport
      actual_source_compact.mul_left
  have h1int : Integrable (fun u : ℝ => u * Real.exp (-u / 2) * nativeOriginalSource u) :=
    ((continuous_id.mul hE).mul nativeOriginalSource_contDiff.continuous).integrable_of_hasCompactSupport
      actual_source_compact.mul_left
  rw [heq, integral_const_mul, integral_sub (h0int.const_mul t) h1int, integral_const_mul]
  rw [nativeOriginalSource_weighted_elementary_moments.2.1,
    nativeOriginalSource_weighted_elementary_moments.2.2.2]
  ring

theorem nativeOriginalLogDriveSummand_continuum_zero (t : ℝ) :
    (∫ x : ℝ in Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
      nativeOriginalLogDriveSummand t x) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1))) (by
      intro x hx
      by_cases hx0 : 0 < x
      · have hxhigh : Real.exp (t + UniversalSinc.fixedScale + 1) < x :=
          lt_of_not_ge (fun h => hx ⟨hx0, h⟩)
        exact nativeOriginalLogDriveSummand_zero_above
          ((Real.exp_lt_exp.mpr (by linarith)).trans hxhigh)
      · exact nativeOriginalLogDriveSummand_zero_below
          ((le_of_not_gt hx0).trans_lt (Real.exp_pos _)))]
  exact nativeOriginalLogDriveSummand_integral_zero t

/-- Actual integer-drive bound with its continuum term discharged internally. -/
theorem nativeOriginalIntegerDrive_abs_le_summand_derivative (t : ℝ) :
    |nativeOriginalIntegerDrive t| ≤
      ∫ x : ℝ in Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        |deriv (nativeOriginalLogDriveSummand t) x| := by
  have h := nativeOriginalIntegerDrive_abel_discrepancy_bound t
  rw [nativeOriginalLogDriveSummand_continuum_zero, sub_zero] at h
  exact h

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_integral_eq_exponential
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_integral_zero
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_continuum_zero
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_abs_le_summand_derivative
