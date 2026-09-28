import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A3: propagation interface

A contact derivative sign alone cannot prevent crossing. The actual canonical
route must supply a neighborhood comparison law with independently controlled
coefficients.
-/

def GroundMultiplicativeComparison
    (lam C : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ t, t ∈ Set.Icc a b →
    deriv lam t ≥ -C t * lam t

def GroundNonnegativityPropagation
    (lam : ℝ → ℝ) (L0 : ℝ) : Prop :=
  ∀ L : ℝ, L0 ≤ L → 0 ≤ lam L0 → 0 ≤ lam L

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
