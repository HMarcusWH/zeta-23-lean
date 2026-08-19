/-
Experimental formal namespace for exceptional-zero route foundations.
No theorem in this subtree may depend on research/RHRC code.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace Zeta23.ExceptionalZero

/-- Distance of a real part from the critical line. -/
def offLineDepth (sigma : ℝ) : ℝ := |sigma - (1 / 2 : ℝ)|

/-- A generic nonnegative scale profile. Concrete residual norms will instantiate this. -/
abbrev ScaleProfile := ℝ → ℝ

/-- Pointwise logarithmic growth quotient at positive scale. Kept elementary until a concrete
    limsup construction is selected and proved useful. -/
def logGrowthQuotient (R : ScaleProfile) (a : ℝ) : ℝ := Real.log (R a) / a

/-- Subexponential upper-bound predicate in an epsilon form. -/
def Subexponential (R : ScaleProfile) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ a : ℝ, A ≤ a → R a ≤ Real.exp (ε * a)

/-- Positive exponential lower-growth predicate in an epsilon-free witness form. -/
def HasExponentialLowerGrowth (R : ScaleProfile) (rate : ℝ) : Prop :=
  0 < rate ∧ ∃ A C : ℝ, 0 < C ∧ ∀ a : ℝ, A ≤ a → C * Real.exp (rate * a) ≤ R a

end Zeta23.ExceptionalZero
