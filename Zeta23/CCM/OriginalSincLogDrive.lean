import Zeta23.CCM.OriginalSincWeightedPoleMoments
import Zeta23.CCM.NativeAbelDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The actual smooth logarithmic integer-drive summand

The extension is literally zero on the nonpositive half-line. Actual compact
source support makes it zero on a positive neighborhood of zero, so smoothness
does not assume a removable singularity of log or sqrt. Its finite integer
sum is the actual original drive. Abel discrepancy is exported with the
remaining continuum integral and derivative norm retained.
-/

noncomputable section

open MeasureTheory Filter Set Finset
open scoped Topology

namespace Zeta23.CCM

def nativeOriginalLogDriveSummand (t x : ℝ) : ℝ :=
  if 0 < x then Real.log x / Real.sqrt x *
    nativeOriginalSource (t - Real.log x) else 0

theorem nativeOriginalLogDriveSummand_zero_below {t x : ℝ}
    (hx : x < Real.exp (t - UniversalSinc.fixedScale)) :
    nativeOriginalLogDriveSummand t x = 0 := by
  unfold nativeOriginalLogDriveSummand
  split_ifs with hpos
  · have hlog : Real.log x < t - UniversalSinc.fixedScale :=
      (Real.log_lt_iff_lt_exp hpos).mpr hx
    have hj : nativeOriginalSource (t - Real.log x) = 0 := by
      apply nativeOriginalSource_supported
      intro hm
      linarith [hm.2]
    rw [hj, mul_zero]
  · rfl

theorem nativeOriginalLogDriveSummand_zero_above {t x : ℝ}
    (hx : Real.exp (t + UniversalSinc.fixedScale) < x) :
    nativeOriginalLogDriveSummand t x = 0 := by
  have hpos : 0 < x := (Real.exp_pos _).trans hx
  have hlog : t + UniversalSinc.fixedScale < Real.log x :=
    (Real.lt_log_iff_exp_lt hpos).mpr hx
  unfold nativeOriginalLogDriveSummand
  rw [if_pos hpos]
  have hj : nativeOriginalSource (t - Real.log x) = 0 := by
    apply nativeOriginalSource_supported
    intro hm
    linarith [hm.1]
  rw [hj, mul_zero]

theorem nativeOriginalLogDriveSummand_contDiff (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (nativeOriginalLogDriveSummand t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hlog := (contDiffAt_id : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x) x).log hx.ne'
    have hroot := (contDiffAt_id : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x) x).sqrt hx.ne'
    have hf : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : ℝ => Real.log y / Real.sqrt y *
          nativeOriginalSource (t - Real.log y)) x :=
      (hlog.div hroot (Real.sqrt_pos.mpr hx).ne').mul
        (nativeOriginalSource_contDiff.contDiffAt.comp x (contDiffAt_const.sub hlog))
    apply hf.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    exact if_pos hy
  · have hbound : x < Real.exp (t - UniversalSinc.fixedScale) :=
      lt_of_le_of_lt (le_of_not_gt hx) (Real.exp_pos _)
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.eventually_mem hbound] with y hy
    exact nativeOriginalLogDriveSummand_zero_below hy

theorem nativeOriginalLogDriveSummand_hasCompactSupport (t : ℝ) :
    HasCompactSupport (nativeOriginalLogDriveSummand t) := by
  apply HasCompactSupport.intro
    (K := Icc (Real.exp (t - UniversalSinc.fixedScale))
      (Real.exp (t + UniversalSinc.fixedScale))) isCompact_Icc
  intro x hx
  by_cases hlow : x < Real.exp (t - UniversalSinc.fixedScale)
  · exact nativeOriginalLogDriveSummand_zero_below hlow
  · apply nativeOriginalLogDriveSummand_zero_above
    exact lt_of_not_ge (fun hh => hx ⟨le_of_not_gt hlow, hh⟩)

theorem nativeOriginalLogDriveSummand_at_nat (t : ℝ) (n : ℕ) :
    nativeOriginalLogDriveSummand t n =
      nativeIntegerDriveCoefficient n * nativeOriginalSource (t - Real.log n) := by
  by_cases hn : n = 0
  · subst n
    simp [nativeOriginalLogDriveSummand, nativeIntegerDriveCoefficient]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [nativeOriginalLogDriveSummand, if_pos hnpos, nativeIntegerDriveCoefficient]

/-- The inclusive integer sum in Abel's formula is the actual original U,
with a unit upper collar ensuring the upper boundary vanishes. -/
theorem nativeOriginalIntegerDrive_eq_abel_sum (t : ℝ) :
    nativeOriginalIntegerDrive t =
      ∑ n ∈ Finset.Icc 0 ⌊Real.exp (t + UniversalSinc.fixedScale + 1)⌋₊,
        nativeOriginalLogDriveSummand t n := by
  rw [nativeOriginalIntegerDrive_eq_history_sum (T := t + 1) (by linarith)]
  have htime : t + 1 + UniversalSinc.fixedScale = t + UniversalSinc.fixedScale + 1 := by ring
  unfold nativeHistoryCutoff
  rw [htime]
  have hset (N : ℕ) : Finset.range (N + 1) = Finset.Icc 0 N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_Icc, Nat.zero_le, true_and]
    omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro n hn
  exact (nativeOriginalLogDriveSummand_at_nat t n).symm

theorem nativeOriginalIntegerDrive_abel_discrepancy_bound (t : ℝ) :
    |nativeOriginalIntegerDrive t -
      ∫ x : ℝ in Set.Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        nativeOriginalLogDriveSummand t x| ≤
      ∫ x : ℝ in Set.Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        |deriv (nativeOriginalLogDriveSummand t) x| := by
  rw [nativeOriginalIntegerDrive_eq_abel_sum]
  apply nativeIntegerAbel_discrepancy_bound (Real.exp_pos _).le
    ((nativeOriginalLogDriveSummand_contDiff t).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  apply nativeOriginalLogDriveSummand_zero_above
  exact Real.exp_lt_exp.mpr (by linarith)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_zero_below
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_zero_above
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_contDiff
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_hasCompactSupport
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_at_nat
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_eq_abel_sum
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_abel_discrepancy_bound
