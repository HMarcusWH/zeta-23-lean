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

end Zeta23.ExceptionalZero
