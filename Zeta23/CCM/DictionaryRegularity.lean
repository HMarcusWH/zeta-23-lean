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
needed for the compact dictionary.  We deliberately use Lean's canonical
`deriv` for the diagonal and residual derivatives: direct `HasDerivAt`
subtraction can elaborate the real normed-space instance through two different
paths in this toolchain.

No explicit formula is invoked here.
-/

/-- Second derivative of the real source potential. -/
def sourcePotentialSecondDerivative (ω : ℝ) (n : ℤ) : ℝ :=
  -Real.sin (2 * Real.pi * (n : ℝ) * ω)
    * (2 * Real.pi * (n : ℝ)) * (2 * Real.pi * (n : ℝ)) / Real.pi

/-- Canonical second derivative of the diagonal source datum. -/
def sourceDiagonalSecondDerivative (ω : ℝ) (n : ℤ) : ℝ :=
  deriv (fun t : ℝ => sourceDiagonalDerivative t n) ω

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

/-- The diagonal derivative is differentiable everywhere. -/
theorem differentiableAt_sourceDiagonalDerivative (ω : ℝ) (n : ℤ) :
    DifferentiableAt ℝ (fun t : ℝ => sourceDiagonalDerivative t n) ω := by
  have hfun : (fun t : ℝ => sourceDiagonalDerivative t n) =
      fun t =>
        2 * Real.cos (2 * Real.pi * (n : ℝ) * t)
          + 2 * t *
            (-Real.sin (2 * Real.pi * (n : ℝ) * t) * (2 * Real.pi * (n : ℝ))) := by
    funext t
    exact sourceDiagonalDerivative_formula t n
  rw [hfun]
  fun_prop

/-- Exact derivative of the diagonal derivative, by the canonical `deriv`. -/
theorem hasDerivAt_sourceDiagonalDerivative (ω : ℝ) (n : ℤ) :
    HasDerivAt (fun t : ℝ => sourceDiagonalDerivative t n)
      (sourceDiagonalSecondDerivative ω n) ω := by
  exact (differentiableAt_sourceDiagonalDerivative ω n).hasDerivAt

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

/-- The diagonal source datum has zero second derivative at `ω = 0`. -/
@[simp] theorem sourceDiagonalSecondDerivative_zero (n : ℤ) :
    sourceDiagonalSecondDerivative 0 n = 0 := by
  unfold sourceDiagonalSecondDerivative
  let a : ℝ := 2 * Real.pi * (n : ℝ)
  have hfun : (fun t : ℝ => sourceDiagonalDerivative t n) =
      fun t => 2 * Real.cos (a * t) + 2 * t * (-Real.sin (a * t) * a) := by
    funext t
    simpa [a] using sourceDiagonalDerivative_formula t n
  rw [hfun]
  have hfirstDiff : DifferentiableAt ℝ (fun t : ℝ => 2 * Real.cos (a * t)) 0 := by
    fun_prop
  have hsecondDiff :
      DifferentiableAt ℝ (fun t : ℝ => 2 * t * (-Real.sin (a * t) * a)) 0 := by
    fun_prop
  rw [deriv_fun_add hfirstDiff hsecondDiff]
  have harg : HasDerivAt (fun t : ℝ => a * t) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  have hfirst : HasDerivAt (fun t : ℝ => 2 * Real.cos (a * t)) 0 0 := by
    simpa using harg.cos.const_mul (2 : ℝ)
  rw [hfirst.deriv]
  have hleftDiff : DifferentiableAt ℝ (fun t : ℝ => 2 * t) 0 := by
    fun_prop
  have hrightDiff : DifferentiableAt ℝ (fun t : ℝ => -Real.sin (a * t) * a) 0 := by
    fun_prop
  rw [deriv_fun_mul hleftDiff hrightDiff]
  simp

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

/-- Canonical derivative of the rank-one-regularized source contraction. -/
def sourceContractRealResidualDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℝ :=
  deriv (sourceContractRealResidual N u) ω

/-- The regularized source contraction is differentiable everywhere. -/
theorem differentiableAt_sourceContractRealResidual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    DifferentiableAt ℝ (sourceContractRealResidual N u) ω := by
  unfold sourceContractRealResidual
  exact (hasDerivAt_sourceContractReal N u ω).differentiableAt.sub (by fun_prop)

/-- Closed first-derivative formula for the regularized source contraction. -/
theorem sourceContractRealResidualDerivative_formula
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    sourceContractRealResidualDerivative N u ω =
      sourceContractRealDerivative N u ω - 2 * (coefficientSumReal N u) ^ 2 := by
  unfold sourceContractRealResidualDerivative sourceContractRealResidual
  have hlin : HasDerivAt
      (fun t : ℝ => 2 * (coefficientSumReal N u) ^ 2 * t)
      (2 * (coefficientSumReal N u) ^ 2) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * (coefficientSumReal N u) ^ 2)
  have h := (hasDerivAt_sourceContractReal N u ω).sub hlin
  exact h.deriv

/-- Exact derivative of the regularized source contraction, by canonical `deriv`. -/
theorem hasDerivAt_sourceContractRealResidual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    HasDerivAt (sourceContractRealResidual N u)
      (sourceContractRealResidualDerivative N u ω) ω := by
  exact (differentiableAt_sourceContractRealResidual N u ω).hasDerivAt

@[simp] theorem sourceContractRealResidual_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealResidual N u 0 = 0 := by
  simp [sourceContractRealResidual]

/-- Removing the rank-one linear mode kills the first derivative at the cutoff endpoint. -/
@[simp] theorem sourceContractRealResidualDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealResidualDerivative N u 0 = 0 := by
  rw [sourceContractRealResidualDerivative_formula,
    sourceContractRealDerivative_zero_eq_two_coefficientSum_sq]
  ring

/-- The same linear subtraction kills the derivative at the folded center endpoint. -/
@[simp] theorem sourceContractRealResidualDerivative_one
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealResidualDerivative N u 1 = 0 := by
  rw [sourceContractRealResidualDerivative_formula,
    sourceContractRealDerivative_one_eq_two_coefficientSum_sq]
  ring

/-- Canonical second derivative of the regularized source contraction. -/
def sourceContractRealResidualSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℝ :=
  deriv (sourceContractRealResidualDerivative N u) ω

/-- The regularized source derivative is differentiable everywhere. -/
theorem differentiableAt_sourceContractRealResidualDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    DifferentiableAt ℝ (sourceContractRealResidualDerivative N u) ω := by
  have hfun : sourceContractRealResidualDerivative N u =
      fun t => sourceContractRealDerivative N u t - 2 * (coefficientSumReal N u) ^ 2 := by
    funext t
    exact sourceContractRealResidualDerivative_formula N u t
  rw [hfun]
  exact (hasDerivAt_sourceContractRealDerivative N u ω).differentiableAt.sub (by fun_prop)

/-- The residual second derivative equals the source second derivative: subtracting
a linear mode changes no second derivative. -/
theorem sourceContractRealResidualSecondDerivative_formula
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    sourceContractRealResidualSecondDerivative N u ω =
      sourceContractRealSecondDerivative N u ω := by
  unfold sourceContractRealResidualSecondDerivative
  have hfun : sourceContractRealResidualDerivative N u =
      fun t => sourceContractRealDerivative N u t - 2 * (coefficientSumReal N u) ^ 2 := by
    funext t
    exact sourceContractRealResidualDerivative_formula N u t
  rw [hfun]
  have hK := hasDerivAt_sourceContractRealDerivative N u ω
  have hconstDiff :
      DifferentiableAt ℝ (fun _ : ℝ => 2 * (coefficientSumReal N u) ^ 2) ω := by
    fun_prop
  rw [deriv_fun_sub hK.differentiableAt hconstDiff, hK.deriv]
  simp

/-- After removing the universal tent mode, the residual also has vanishing
second derivative at the cutoff endpoint. -/
@[simp] theorem sourceContractRealResidualSecondDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealResidualSecondDerivative N u 0 = 0 := by
  rw [sourceContractRealResidualSecondDerivative_formula,
    sourceContractRealSecondDerivative_zero]

end Zeta23.CCM
