import Zeta23.ExceptionalZero.Defs

namespace Zeta23.ExceptionalZero

/-- A profile bounded by 1 is subexponential. This is a deliberately elementary base lemma. -/
theorem subexponential_of_le_one (R : ScaleProfile)
    (hR : ∀ a : ℝ, R a ≤ 1) : Subexponential R := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro a ha
  calc
    R a ≤ 1 := hR a
    _ ≤ Real.exp (ε * a) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hε.le ha)

/-- A genuinely positive exponential lower bound is incompatible with subexponential growth.
This is the abstract contradiction seam consumed by the exceptional-zero route once its concrete
zero-side lower bound and prime-side upper bound have both been proved. -/
theorem not_subexponential_of_hasExponentialLowerGrowth
    {R : ScaleProfile} {rate : ℝ}
    (hgrowth : HasExponentialLowerGrowth R rate) : ¬ Subexponential R := by
  rintro hsub
  obtain ⟨hrate, A, C, hC, hlower⟩ := hgrowth
  obtain ⟨B, hupper⟩ := hsub (rate / 2) (half_pos hrate)
  let T : ℝ := 2 * (1 - Real.log C) / rate
  let a : ℝ := max A (max B T)
  have hA : A ≤ a := le_max_left _ _
  have hB : B ≤ a := le_trans (le_max_left B T) (le_max_right A (max B T))
  have hT : T ≤ a := le_trans (le_max_right B T) (le_max_right A (max B T))
  have hmul : 2 * (1 - Real.log C) ≤ a * rate := by
    exact (div_le_iff₀ hrate).mp hT
  have hlog : 0 < Real.log C + (rate / 2) * a := by
    nlinarith
  have hfactor : 1 < C * Real.exp ((rate / 2) * a) := by
    calc
      1 = Real.exp 0 := by simp
      _ < Real.exp (Real.log C + (rate / 2) * a) := Real.exp_lt_exp.mpr hlog
      _ = C * Real.exp ((rate / 2) * a) := by
        rw [Real.exp_add, Real.exp_log hC]
  have hhalfpos : 0 < Real.exp ((rate / 2) * a) := Real.exp_pos _
  have hstrict : Real.exp ((rate / 2) * a) < C * Real.exp (rate * a) := by
    calc
      Real.exp ((rate / 2) * a)
          = 1 * Real.exp ((rate / 2) * a) := by ring
      _ < (C * Real.exp ((rate / 2) * a)) * Real.exp ((rate / 2) * a) :=
        mul_lt_mul_of_pos_right hfactor hhalfpos
      _ = C * Real.exp (rate * a) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hlo := hlower a hA
  have hup := hupper a hB
  linarith

end Zeta23.ExceptionalZero
