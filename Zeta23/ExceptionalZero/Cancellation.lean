import Zeta23.ExceptionalZero.RMSGrowth

namespace Zeta23.ExceptionalZero

/-- A single probe contribution is bounded above by the full finite square norm. This is the
    elementary algebraic reason a probe-family norm can retain information that pointwise sums may cancel. -/
theorem single_probe_sq_le_probeSqNorm {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : ι → ℝ → ℝ) (i : ι) (a : ℝ) :
    (R i a) ^ 2 ≤ probeSqNorm R a := by
  unfold probeSqNorm
  exact Finset.single_le_sum (fun j _ => sq_nonneg (R j a)) (Finset.mem_univ i)

end Zeta23.ExceptionalZero
