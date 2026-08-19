import Zeta23.ExceptionalZero.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace Zeta23.ExceptionalZero

/-- Abstract multi-probe square norm. The finite probe set keeps the first formal layer independent
    of measure-theoretic choices; later routes may replace or extend it. -/
def probeSqNorm {ι : Type} [Fintype ι] (R : ι → ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑ i, (R i a) ^ 2

end Zeta23.ExceptionalZero
