import Zeta23.CCM.NativePositiveCompletion
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual floor completion in logarithmic cell coordinates

The density below is the actual `a(log u)/u` which a future measure
substitution must integrate. This file establishes its exact cell formula
and the pointwise bound needed by the direct mass route. No substitution,
integral value, infinite tail or complete kernel mass is assumed or claimed.
-/

noncomputable section

namespace Zeta23.CCM

def nativePositiveCompletionLogDensity (u : ℝ) : ℝ :=
  nativePositiveCompletion (Real.log u) / u

theorem nativePositiveCompletionLogDensity_cell {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu : (n : ℝ) ≤ u) (huupper : u < (n : ℝ) + 1) :
    nativePositiveCompletionLogDensity u =
      (n : ℝ) * ((n : ℝ) + 1 - u) * u ^ (-5 / 2 : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hupos : 0 < u := hnreal.trans_le hu
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hunone : 1 ≤ u := hn1.trans hu
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hunone
  have hfloor : ⌊u⌋₊ = n := (Nat.floor_eq_iff hupos.le).mpr ⟨hu, huupper⟩
  have hpow : Real.exp (-(3 * Real.log u / 2)) / u = u ^ (-5 / 2 : ℝ) := by
    have hexp : Real.exp (-(3 * Real.log u / 2)) = u ^ (-3 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hupos]
      congr 1
      ring
    rw [hexp]
    have heq : (-5 / 2 : ℝ) = -3 / 2 + (-1) := by norm_num
    rw [heq, Real.rpow_add hupos, Real.rpow_neg_one]
    ring
  unfold nativePositiveCompletionLogDensity nativePositiveCompletion
  rw [if_pos hlog, Real.exp_log hupos, hfloor]
  calc
    _ = (n : ℝ) * ((n : ℝ) + 1 - u) *
        (Real.exp (-(3 * Real.log u / 2)) / u) := by ring
    _ = _ := by rw [hpow]

/-- The actual cell density has a linear cap, whose integral would be
`1/(2*n^(3/2))`. That integration remains a separate obligation. -/
theorem nativePositiveCompletionLogDensity_cell_le {n : ℕ} (hn : 0 < n)
    {u : ℝ} (hu : (n : ℝ) ≤ u) (huupper : u < (n : ℝ) + 1) :
    nativePositiveCompletionLogDensity u ≤
      (n : ℝ) ^ (-3 / 2 : ℝ) * ((n : ℝ) + 1 - u) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor : 0 ≤ (n : ℝ) + 1 - u := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hnreal hu
    (by norm_num : (-5 / 2 : ℝ) ≤ 0)
  have hcollapse : (n : ℝ) * (n : ℝ) ^ (-5 / 2 : ℝ) =
      (n : ℝ) ^ (-3 / 2 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-5 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (-5 / 2 : ℝ)) := (Real.rpow_add hnreal _ _).symm
      _ = _ := by norm_num
  rw [nativePositiveCompletionLogDensity_cell hn hu huupper]
  calc
    _ = ((n : ℝ) * u ^ (-5 / 2 : ℝ)) * ((n : ℝ) + 1 - u) := by ring
    _ ≤ ((n : ℝ) * (n : ℝ) ^ (-5 / 2 : ℝ)) * ((n : ℝ) + 1 - u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hnreal.le) hfactor
    _ = _ := by rw [hcollapse]

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_cell
#print axioms Zeta23.CCM.nativePositiveCompletionLogDensity_cell_le
