import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A3: propagation contract

A contact derivative sign alone cannot prevent crossing. The actual route must
supply a neighborhood comparison law with independently controlled
coefficients. This module records that obligation and a regression
counterexample shape without claiming the canonical inequality.
-/

def GroundMultiplicativeComparison
    (lam C : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ t, t ∈ Set.Icc a b →
    deriv lam t ≥ -C t * lam t

def CanonicalGroundPropagation : Prop := False

def cubicCrossingRegression (t : ℝ) : ℝ := -t ^ 3

@[simp] theorem cubicCrossingRegression_zero :
    cubicCrossingRegression 0 = 0 := by
  simp [cubicCrossingRegression]

theorem cubicCrossingRegression_negative_of_pos
    {t : ℝ} (ht : 0 < t) :
    cubicCrossingRegression t < 0 := by
  unfold cubicCrossingRegression
  nlinarith [sq_pos_of_pos ht]

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicCrossingRegression_zero
#print axioms Zeta23.CCM.cubicCrossingRegression_negative_of_pos
