import Zeta23.CCM.DictionaryAnalysis
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

open Set
open scoped BigOperators

/-! # Second-order control of the dictionary seam

The first-order calculation in `DictionaryAnalysis` shows that both source
endpoints have derivative matrix `2 * 1 1ᵀ`.  This file records the next jet
needed for the compact dictionary: the source derivative has zero derivative at
`ω = 0`, so after subtracting the universal linear rank-one mode the residual
has vanishing value, first derivative and second derivative at the cutoff end.

No explicit formula is invoked here.
-/

/-- Second derivative of the real source potential. -/
def sourcePotentialSecondDerivative (ω : ℝ) (n : ℤ) : ℝ :=
  -Real.sin (2 * Real.pi * (n : ℝ) * ω)
    * (2 * Real.pi * (n : ℝ)) * (2 * Real.pi * (n : ℝ)) / Real.pi

/-- Second derivative of the real diagonal source datum. -/
def sourceDiagonalSecondDerivative (ω : ℝ) (n : ℤ) : ℝ :=
  let a := 2 * Real.pi * (n : ℝ)
  -4 * Real.sin (a * ω) * a - 2 * ω * Real.cos (a * ω) * a ^ 2

/-- Entrywise second source derivative. -/
def sourceEntrySecondDerivative (ω : ℝ) (n m : ℤ) : ℝ :=
  if n = m then sourceDiagonalSecondDerivative ω n
  else
    (sourcePotentialSecondDerivative ω n - sourcePotentialSecondDerivative ω m)
      / ((n - m : ℤ) : ℝ)

/-- Exact derivative of `sourcePotentialDerivative`. -/
theorem hasDerivAt_sourcePotentialDerivative (ω : ℝ) (n : ℤ) :
    HasDerivAt (fun t : ℝ => sourcePotentialDerivative t n)
      (sourcePotentialSecondDerivative ω n) ω := by
  have harg : HasDerivAt (fun t : ℝ => 2 * Real.pi * (n : ℝ) * t)
      (2 * Real.pi * (n : ℝ)) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * Real.pi * (n : ℝ))
  have hcos := harg.cos
  have hscaled := hcos.mul_const (2 * Real.pi * (n : ℝ))
  have hquot := hscaled.div_const Real.pi
  simpa [sourcePotentialDerivative, sourcePotentialSecondDerivative, mul_assoc] using hquot

/-- Exact derivative of `sourceDiagonalDerivative`. -/
theorem hasDerivAt_sourceDiagonalDerivative (ω : ℝ) (n : ℤ) :
    HasDerivAt (fun t : ℝ => sourceDiagonalDerivative t n)
      (sourceDiagonalSecondDerivative ω n) ω := by
  let a : ℝ := 2 * Real.pi * (n : ℝ)
  have harg : HasDerivAt (fun t : ℝ => a * t) a ω := by
    simpa [a] using (hasDerivAt_id ω).const_mul a
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (a * t))
      (-Real.sin (a * ω) * a) ω := by
    simpa using harg.cos
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (a * t))
      (Real.cos (a * ω) * a) ω := by
    simpa using harg.sin
  have hfirst := hcos.const_mul (2 : ℝ)
  have hleft : HasDerivAt (fun t : ℝ => 2 * t) 2 ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 : ℝ)
  have hright := hsin.neg.mul_const a
  have hsecond := hleft.mul hright
  have hsum := hfirst.add hsecond
  have hfun : (fun t : ℝ => sourceDiagonalDerivative t n) =
      fun t => 2 * Real.cos (a * t) + 2 * t * (-Real.sin (a * t) * a) := by
    funext t
    rw [sourceDiagonalDerivative_formula]
    simp [a, mul_assoc]
  rw [hfun]
  convert hsum using 1 <;>
    simp [sourceDiagonalSecondDerivative, a] <;> ring

/-- Exact derivative of every source-entry derivative. -/
theorem hasDerivAt_sourceEntryDerivative (ω : ℝ) (n m : ℤ) :
    HasDerivAt (fun t : ℝ => sourceEntryDerivative t n m)
      (sourceEntrySecondDerivative ω n m) ω := by
  by_cases h : n = m
  · subst m
    simpa [sourceEntryDerivative, sourceEntrySecondDerivative] using
      hasDerivAt_sourceDiagonalDerivative ω n
  · have hnum := (hasDerivAt_sourcePotentialDerivative ω n).sub
        (hasDerivAt_sourcePotentialDerivative ω m)
    have hquot := hnum.div_const (((n - m : ℤ) : ℝ))
    simpa [sourceEntryDerivative, sourceEntrySecondDerivative, h] using hquot

@[simp] theorem sourcePotentialSecondDerivative_zero (n : ℤ) :
    sourcePotentialSecondDerivative 0 n = 0 := by
  simp [sourcePotentialSecondDerivative]

@[simp] theorem sourceDiagonalSecondDerivative_zero (n : ℤ) :
    sourceDiagonalSecondDerivative 0 n = 0 := by
  simp [sourceDiagonalSecondDerivative]

/-- Every source entry has zero second derivative at the cutoff endpoint. -/
@[simp] theorem sourceEntrySecondDerivative_zero (n m : ℤ) :
    sourceEntrySecondDerivative 0 n m = 0 := by
  by_cases h : n = m
  · subst m
    simp [sourceEntrySecondDerivative]
  · simp [sourceEntrySecondDerivative, h]

/-- Second derivative of the real quadratic source contraction. -/
def sourceContractRealSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℝ :=
  ∑ i, ∑ j,
    u i * sourceEntrySecondDerivative ω (centeredIndex N i) (centeredIndex N j) * u j

/-- The first-derivative contraction is differentiable entrywise. -/
theorem hasDerivAt_sourceContractRealDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    HasDerivAt (sourceContractRealDerivative N u)
      (sourceContractRealSecondDerivative N u ω) ω := by
  unfold sourceContractRealDerivative sourceContractRealSecondDerivative
  apply HasDerivAt.fun_sum
  intro i hi
  apply HasDerivAt.fun_sum
  intro j hj
  have hentry := hasDerivAt_sourceEntryDerivative
    ω (centeredIndex N i) (centeredIndex N j)
  simpa [mul_assoc] using (hentry.const_mul (u i)).mul_const (u j)

/-- The source quadratic form has zero second derivative at `ω = 0`. -/
@[simp] theorem sourceContractRealSecondDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealSecondDerivative N u 0 = 0 := by
  simp [sourceContractRealSecondDerivative]

/-- Real source contraction vanishes at `ω = 0`. -/
@[simp] theorem sourceContractReal_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractReal N u 0 = 0 := by
  unfold sourceContractReal sourceEntryReal sourcePotentialReal sourceDiagonalReal
  simp

/-- Derivative of the rank-one-regularized source contraction. -/
def sourceContractRealResidualDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℝ :=
  sourceContractRealDerivative N u ω - 2 * (coefficientSumReal N u) ^ 2

/-- Exact derivative of the regularized source contraction. -/
theorem hasDerivAt_sourceContractRealResidual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    HasDerivAt (sourceContractRealResidual N u)
      (sourceContractRealResidualDerivative N u ω) ω := by
  have hlin : HasDerivAt
      (fun t : ℝ => 2 * (coefficientSumReal N u) ^ 2 * t)
      (2 * (coefficientSumReal N u) ^ 2) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * (coefficientSumReal N u) ^ 2)
  simpa [sourceContractRealResidual, sourceContractRealResidualDerivative] using
    (hasDerivAt_sourceContractReal N u ω).sub hlin

@[simp] theorem sourceContractRealResidual_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealResidual N u 0 = 0 := by
  simp [sourceContractRealResidual]

/-- Removing the rank-one linear mode kills the first derivative at the cutoff endpoint. -/
@[simp] theorem sourceContractRealResidualDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealResidualDerivative N u 0 = 0 := by
  rw [sourceContractRealResidualDerivative,
    sourceContractRealDerivative_zero_eq_two_coefficientSum_sq]
  ring

/-- The same linear subtraction kills the derivative at the folded center endpoint. -/
@[simp] theorem sourceContractRealResidualDerivative_one
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealResidualDerivative N u 1 = 0 := by
  rw [sourceContractRealResidualDerivative,
    sourceContractRealDerivative_one_eq_two_coefficientSum_sq]
  ring

/-- The regularized source derivative has zero derivative at the cutoff endpoint. -/
theorem hasDerivAt_sourceContractRealResidualDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    HasDerivAt (sourceContractRealResidualDerivative N u) 0 0 := by
  have hK := hasDerivAt_sourceContractRealDerivative N u 0
  have hconst : HasDerivAt
      (fun _ : ℝ => 2 * (coefficientSumReal N u) ^ 2) 0 0 := by
    simpa using hasDerivAt_const (x := (0 : ℝ))
      (c := 2 * (coefficientSumReal N u) ^ 2)
  simpa [sourceContractRealResidualDerivative] using hK.sub hconst

end Zeta23.CCM
