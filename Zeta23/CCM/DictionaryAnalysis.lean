import Zeta23.CCM.FiniteDictionary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators

/-! # Analytic control for the finite dictionary

PR #37 begins by isolating the first-order seam of the compact dictionary test.
The finite source matrix is real-valued, so the derivative calculation is made
in a real shadow that is proved entrywise equal to the existing complex source
matrix.  This keeps ordinary one-variable `HasDerivAt` available while retaining
the theorem-authoritative PR #34/#35 source object.

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

/-- Derivative of the diagonal source datum, in product-rule normal form. -/
def sourceDiagonalDerivative (ω : ℝ) (n : ℤ) : ℝ :=
  2 * Real.cos (2 * Real.pi * (n : ℝ) * ω)
    + 2 * ω * (-Real.sin (2 * Real.pi * (n : ℝ) * ω) * (2 * Real.pi * (n : ℝ)))

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

/-- Exact derivative of the real diagonal source datum. -/
theorem hasDerivAt_sourceDiagonalReal (ω : ℝ) (n : ℤ) :
    HasDerivAt (fun t : ℝ => sourceDiagonalReal t n) (sourceDiagonalDerivative ω n) ω := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * Real.pi * (n : ℝ) * t)
      (2 * Real.pi * (n : ℝ)) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * Real.pi * (n : ℝ))
  have hcos := hlin.cos
  have hprod : HasDerivAt
      (fun t : ℝ => t * Real.cos (2 * Real.pi * (n : ℝ) * t))
      (Real.cos (2 * Real.pi * (n : ℝ) * ω)
        + ω * (-Real.sin (2 * Real.pi * (n : ℝ) * ω) * (2 * Real.pi * (n : ℝ)))) ω := by
    simpa using (hasDerivAt_id ω).mul hcos
  have hscaled := hprod.const_mul 2
  simpa [sourceDiagonalReal, sourceDiagonalDerivative, mul_add, mul_assoc] using hscaled

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
  simp [sourceDiagonalDerivative]

@[simp] theorem sourceDiagonalDerivative_one (n : ℤ) :
    sourceDiagonalDerivative 1 n = 2 := by
  unfold sourceDiagonalDerivative
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

end Zeta23.CCM
