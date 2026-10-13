import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace Zeta23.CCM

/-!
The actual causal floor kernel, including its integer seam convention. This
module proves its positivity and pointwise envelope. Its Laplace identity,
strict mass bound, and original-source Y equation are not proved here.
-/

def nativePositiveCompletion (t : ℝ) : ℝ :=
  if 0 ≤ t then
    Real.exp (-(3 * t / 2)) * (⌊Real.exp t⌋₊ : ℝ) *
      ((⌊Real.exp t⌋₊ : ℝ) + 1 - Real.exp t)
  else 0

theorem nativePositiveCompletion_nonneg (t : ℝ) :
    0 ≤ nativePositiveCompletion t := by
  unfold nativePositiveCompletion
  split_ifs with ht
  · have hfloor : Real.exp t < (⌊Real.exp t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
      (by linarith)
  · exact le_refl 0

theorem nativePositiveCompletion_le_exp (t : ℝ) :
    nativePositiveCompletion t ≤ Real.exp (-(t / 2)) := by
  unfold nativePositiveCompletion
  split_ifs with ht
  · have hx : 0 ≤ Real.exp t := (Real.exp_pos t).le
    have hn : (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp t := Nat.floor_le hx
    have hn0 : (0 : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := Nat.cast_nonneg _
    have hfactor : (⌊Real.exp t⌋₊ : ℝ) *
        ((⌊Real.exp t⌋₊ : ℝ) + 1 - Real.exp t) ≤ Real.exp t := by
      nlinarith
    calc
      _ = Real.exp (-(3 * t / 2)) * ((⌊Real.exp t⌋₊ : ℝ) *
          ((⌊Real.exp t⌋₊ : ℝ) + 1 - Real.exp t)) := by ring
      _ ≤ Real.exp (-(3 * t / 2)) * Real.exp t :=
        mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
      _ = Real.exp (-(t / 2)) := by rw [← Real.exp_add]; congr 1; ring
  · exact (Real.exp_pos _).le

theorem nativePositiveCompletion_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    nativePositiveCompletion t = 0 := by
  simp [nativePositiveCompletion, not_le.mpr ht]

theorem nativePositiveCompletion_zero : nativePositiveCompletion 0 = 1 := by
  norm_num [nativePositiveCompletion]

end Zeta23.CCM
