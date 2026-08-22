import Zeta23.CCM.FiniteDictionary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators

/-! # Analytic control for the finite dictionary

PR #37 isolates the first-order seam of the compact dictionary test.  The finite
source matrix is real-valued, so the derivative calculation is made in a real
shadow that is proved entrywise equal to the existing complex source matrix.
This keeps ordinary one-variable `HasDerivAt` available while retaining the
theorem-authoritative PR #34/#35 source object.

No explicit formula is invoked in this module.
-/

/-- Real-valued source potential underlying `sourcePotential`. -/
def sourcePotentialReal (ω : ℝ) (n : ℤ) : ℝ :=
  Real.sin (2 * Real.pi * (n : ℝ) * ω) / Real.pi

/-- Real-valued diagonal datum underlying `sourceDiagonal`. -/
def sourceDiagonalReal (ω : ℝ) (n : ℤ) : ℝ :=
  2 * ω * Real.cos (2 * Real.pi * (n : ℝ) * ω)

/-- Real-valued elementary source entry, synchronized below with `sourceEntry`. -/
def sourceEntryReal (ω : ℝ) (n m : ℤ) : ℝ :=
  if n = m then sourceDiagonalReal ω n
  else (sourcePotentialReal ω n - sourcePotentialReal ω m) / ((n - m : ℤ) : ℝ)

@[simp] theorem sourcePotential_eq_ofReal (ω : ℝ) (n : ℤ) :
    sourcePotential ω n = (sourcePotentialReal ω n : ℂ) := rfl

@[simp] theorem sourceDiagonal_eq_ofReal (ω : ℝ) (n : ℤ) :
    sourceDiagonal ω n = (sourceDiagonalReal ω n : ℂ) := rfl

/-- The real analytic shadow is exactly the existing complex source entry. -/
theorem sourceEntry_eq_ofReal (ω : ℝ) (n m : ℤ) :
    sourceEntry ω n m = (sourceEntryReal ω n m : ℂ) := by
  by_cases h : n = m
  · subst m
    simp [sourceEntryReal]
  · rw [sourceEntry_of_ne ω h]
    simp [sourceEntryReal, h, sourcePotentialReal]

/-- Derivative of the source potential with respect to the source coordinate,
kept in the exact algebraic shape produced by `HasDerivAt.sin`. -/
def sourcePotentialDerivative (ω : ℝ) (n : ℤ) : ℝ :=
  Real.cos (2 * Real.pi * (n : ℝ) * ω) * (2 * Real.pi * (n : ℝ)) / Real.pi

/-- Canonical derivative of the diagonal source datum.  Defining this through
`deriv` keeps the theorem statement on Lean's canonical real normed-space
instance; the closed formula is proved separately below. -/
def sourceDiagonalDerivative (ω : ℝ) (n : ℤ) : ℝ :=
  deriv (fun t : ℝ => sourceDiagonalReal t n) ω

/-- Entrywise source derivative. -/
def sourceEntryDerivative (ω : ℝ) (n m : ℤ) : ℝ :=
  if n = m then sourceDiagonalDerivative ω n
  else (sourcePotentialDerivative ω n - sourcePotentialDerivative ω m) / ((n - m : ℤ) : ℝ)

/-- Exact derivative of the real source potential. -/
theorem hasDerivAt_sourcePotentialReal (ω : ℝ) (n : ℤ) :
    HasDerivAt (fun t : ℝ => sourcePotentialReal t n) (sourcePotentialDerivative ω n) ω := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * (n : ℝ) * t)
      (2 * Real.pi * (n : ℝ)) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * Real.pi * (n : ℝ))
  have hsin := hlin.sin
  simpa [sourcePotentialReal, sourcePotentialDerivative] using hsin.div_const Real.pi

/-- The diagonal datum is differentiable everywhere. -/
theorem differentiableAt_sourceDiagonalReal (ω : ℝ) (n : ℤ) :
    DifferentiableAt ℝ (fun t : ℝ => sourceDiagonalReal t n) ω := by
  unfold sourceDiagonalReal
  fun_prop

/-- Exact derivative of the real diagonal source datum, by the canonical
`deriv` chosen above. -/
theorem hasDerivAt_sourceDiagonalReal (ω : ℝ) (n : ℤ) :
    HasDerivAt (fun t : ℝ => sourceDiagonalReal t n) (sourceDiagonalDerivative ω n) ω := by
  exact (differentiableAt_sourceDiagonalReal ω n).hasDerivAt

/-- Closed product-rule formula for the diagonal derivative. -/
theorem sourceDiagonalDerivative_formula (ω : ℝ) (n : ℤ) :
    sourceDiagonalDerivative ω n =
      2 * Real.cos (2 * Real.pi * (n : ℝ) * ω)
        + 2 * ω *
          (-Real.sin (2 * Real.pi * (n : ℝ) * ω) * (2 * Real.pi * (n : ℝ))) := by
  unfold sourceDiagonalDerivative sourceDiagonalReal
  have hleft : DifferentiableAt ℝ (fun t : ℝ => 2 * t) ω := by fun_prop
  have harg : HasDerivAt (fun t : ℝ => 2 * Real.pi * (n : ℝ) * t)
      (2 * Real.pi * (n : ℝ)) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * Real.pi * (n : ℝ))
  have hright : DifferentiableAt ℝ
      (fun t : ℝ => Real.cos (2 * Real.pi * (n : ℝ) * t)) ω := harg.cos.differentiableAt
  rw [deriv_fun_mul hleft hright]
  have hleftDeriv : deriv (fun t : ℝ => 2 * t) ω = 2 := by
    simpa using ((hasDerivAt_id ω).const_mul 2).deriv
  have hrightDeriv :
      deriv (fun t : ℝ => Real.cos (2 * Real.pi * (n : ℝ) * t)) ω =
        -Real.sin (2 * Real.pi * (n : ℝ) * ω) * (2 * Real.pi * (n : ℝ)) := by
    exact harg.cos.deriv
  rw [hleftDeriv, hrightDeriv]

/-- Exact derivative of every real source entry. -/
theorem hasDerivAt_sourceEntryReal (ω : ℝ) (n m : ℤ) :
    HasDerivAt (fun t : ℝ => sourceEntryReal t n m) (sourceEntryDerivative ω n m) ω := by
  by_cases h : n = m
  · subst m
    simpa [sourceEntryReal, sourceEntryDerivative] using hasDerivAt_sourceDiagonalReal ω n
  · have hnum := (hasDerivAt_sourcePotentialReal ω n).sub
        (hasDerivAt_sourcePotentialReal ω m)
    have hquot := hnum.div_const (((n - m : ℤ) : ℝ))
    simpa [sourceEntryReal, sourceEntryDerivative, h] using hquot

@[simp] theorem sourcePotentialDerivative_zero (n : ℤ) :
    sourcePotentialDerivative 0 n = 2 * (n : ℝ) := by
  unfold sourcePotentialDerivative
  simp
  field_simp [Real.pi_ne_zero]

@[simp] theorem sourcePotentialDerivative_one (n : ℤ) :
    sourcePotentialDerivative 1 n = 2 * (n : ℝ) := by
  unfold sourcePotentialDerivative
  rw [show 2 * Real.pi * (n : ℝ) * 1 = (n : ℝ) * (2 * Real.pi) by ring]
  rw [Real.cos_int_mul_two_pi]
  field_simp [Real.pi_ne_zero]

@[simp] theorem sourceDiagonalDerivative_zero (n : ℤ) :
    sourceDiagonalDerivative 0 n = 2 := by
  rw [sourceDiagonalDerivative_formula]
  simp

@[simp] theorem sourceDiagonalDerivative_one (n : ℤ) :
    sourceDiagonalDerivative 1 n = 2 := by
  rw [sourceDiagonalDerivative_formula]
  rw [show 2 * Real.pi * (n : ℝ) * 1 = (n : ℝ) * (2 * Real.pi) by ring]
  rw [Real.cos_int_mul_two_pi]
  have hsin : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_int_mul_two_pi 0 n
  rw [hsin]
  ring

/-- Every source entry has endpoint derivative `2` at `ω = 0`.  Thus the
endpoint derivative matrix is `2 * 1 1ᵀ`, not `2I`. -/
@[simp] theorem sourceEntryDerivative_zero (n m : ℤ) :
    sourceEntryDerivative 0 n m = 2 := by
  by_cases h : n = m
  · subst m
    simp [sourceEntryDerivative]
  · rw [sourceEntryDerivative, if_neg h]
    simp only [sourcePotentialDerivative_zero]
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
    field_simp [hnmR]
    push_cast
    ring

/-- Every source entry has the same endpoint derivative `2` at `ω = 1`. -/
@[simp] theorem sourceEntryDerivative_one (n m : ℤ) :
    sourceEntryDerivative 1 n m = 2 := by
  by_cases h : n = m
  · subst m
    simp [sourceEntryDerivative]
  · rw [sourceEntryDerivative, if_neg h]
    simp only [sourcePotentialDerivative_one]
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
    field_simp [hnmR]
    push_cast
    ring

/-- Real quadratic source contraction for a real coefficient vector. -/
def sourceContractReal (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℝ :=
  ∑ i, ∑ j, u i * sourceEntryReal ω (centeredIndex N i) (centeredIndex N j) * u j

/-- Its exact derivative, obtained entrywise. -/
def sourceContractRealDerivative (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℝ :=
  ∑ i, ∑ j, u i * sourceEntryDerivative ω (centeredIndex N i) (centeredIndex N j) * u j

/-- The full finite real source contraction is differentiable for every source coordinate. -/
theorem hasDerivAt_sourceContractReal
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    HasDerivAt (sourceContractReal N u) (sourceContractRealDerivative N u ω) ω := by
  unfold sourceContractReal sourceContractRealDerivative
  apply HasDerivAt.fun_sum
  intro i hi
  apply HasDerivAt.fun_sum
  intro j hj
  have hentry := hasDerivAt_sourceEntryReal ω (centeredIndex N i) (centeredIndex N j)
  simpa [mul_assoc] using (hentry.const_mul (u i)).mul_const (u j)

/-- Endpoint derivative of the real quadratic source contraction, before
factorization into the square of the coefficient sum. -/
theorem sourceContractRealDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealDerivative N u 0 =
      ∑ i, ∑ j, u i * 2 * u j := by
  simp [sourceContractRealDerivative]

/-- The same raw endpoint derivative occurs at `ω = 1`. -/
theorem sourceContractRealDerivative_one
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealDerivative N u 1 =
      ∑ i, ∑ j, u i * 2 * u j := by
  simp [sourceContractRealDerivative]

/-- Sum of the real centered-grid coefficients.  This single linear functional
carries the complete first-order seam of the folded dictionary. -/
def coefficientSumReal (N : ℕ) (u : Fin (2 * N + 1) → ℝ) : ℝ :=
  ∑ i, u i

/-- The raw endpoint double sum is exactly the rank-one coefficient-sum mode. -/
theorem endpointDoubleSum_eq_two_coefficientSum_sq
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    (∑ i, ∑ j, u i * 2 * u j) = 2 * (coefficientSumReal N u) ^ 2 := by
  unfold coefficientSumReal
  calc
    (∑ i, ∑ j, u i * 2 * u j)
        = ∑ i, (u i * 2) * (∑ j, u j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
    _ = (∑ i, u i * 2) * (∑ j, u j) := by
          rw [← Finset.sum_mul]
    _ = ((∑ i, u i) * 2) * (∑ j, u j) := by
          rw [← Finset.sum_mul]
    _ = 2 * (∑ i, u i) ^ 2 := by ring

/-- Endpoint derivative at `ω = 0`, in its canonical rank-one form. -/
theorem sourceContractRealDerivative_zero_eq_two_coefficientSum_sq
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealDerivative N u 0 = 2 * (coefficientSumReal N u) ^ 2 := by
  rw [sourceContractRealDerivative_zero,
    endpointDoubleSum_eq_two_coefficientSum_sq]

/-- Endpoint derivative at `ω = 1`, in the same canonical rank-one form. -/
theorem sourceContractRealDerivative_one_eq_two_coefficientSum_sq
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    sourceContractRealDerivative N u 1 = 2 * (coefficientSumReal N u) ^ 2 := by
  rw [sourceContractRealDerivative_one,
    endpointDoubleSum_eq_two_coefficientSum_sq]

/-- The real source contraction is exactly the theorem-authoritative complex
contraction after coercing the coefficient vector. -/
theorem sourceContract_eq_ofReal
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    sourceContract N (fun i => (u i : ℂ)) ω = (sourceContractReal N u ω : ℂ) := by
  unfold sourceContract quadraticForm sourceContractReal
  simp_rw [sourceMatrix_apply, sourceEntry_eq_ofReal, Complex.conj_ofReal]
  push_cast

/-- Subtract the universal rank-one linear source mode.  Its derivative vanishes
at both source endpoints by the preceding theorems. -/
def sourceContractRealResidual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℝ :=
  sourceContractReal N u ω - 2 * (coefficientSumReal N u) ^ 2 * ω

/-- Physical-space residual after removing the universal tent mode.  The
already-existing clamped aperture coordinate is exactly the standard tent. -/
def dictionaryResidualReal
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    sourceContractRealResidual N u (dictionaryApertureCoord L y)

/-- Exact seam decomposition for real coefficient vectors:
`dictionaryTest = coefficientSum^2 * tent + residual`.
No smoothness is claimed here; that is the next analytic gate. -/
theorem dictionaryTest_ofReal_eq_tent_add_residual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) (y : ℝ) :
    dictionaryTest N (fun i => (u i : ℂ)) L y =
      (((coefficientSumReal N u) ^ 2 * dictionaryApertureCoord L y
          + dictionaryResidualReal N u L y : ℝ) : ℂ) := by
  rw [dictionaryTest_eq_clamped N (fun i => (u i : ℂ)) hL y]
  simp only [dictionaryKernel]
  rw [sourceContract_eq_ofReal]
  unfold dictionaryResidualReal sourceContractRealResidual
  push_cast
  ring

end Zeta23.CCM
