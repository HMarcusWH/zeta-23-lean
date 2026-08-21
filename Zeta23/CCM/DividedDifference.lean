import Zeta23.CCM.FiniteMatrix
import Zeta23.ExceptionalZero.DisplacementTransfer

noncomputable section

namespace Zeta23.CCM

open Matrix

/-! # Generic divided-difference matrices

This file isolates the algebraic chassis behind the finite CCM displacement law.
The diagonal data are supplied independently: displacement only sees the
source values `ψ`, while a later analytic specialization may identify the
diagonal with derivative data.
-/

/-- Divided-difference entry with independently supplied diagonal data. -/
def dividedDifferenceEntry (ψ d : ℤ → ℂ) (n m : ℤ) : ℂ :=
  if n = m then d n else (ψ n - ψ m) / (((n - m : ℤ) : ℂ))

@[simp] theorem dividedDifferenceEntry_self (ψ d : ℤ → ℂ) (n : ℤ) :
    dividedDifferenceEntry ψ d n n = d n := by
  simp [dividedDifferenceEntry]

theorem dividedDifferenceEntry_of_ne (ψ d : ℤ → ℂ) {n m : ℤ} (h : n ≠ m) :
    dividedDifferenceEntry ψ d n m = (ψ n - ψ m) / (((n - m : ℤ) : ℂ)) := by
  simp [dividedDifferenceEntry, h]

/-- The defining divided-difference identity. It is valid on the diagonal too,
where both sides vanish independently of the chosen diagonal data. -/
theorem sub_mul_dividedDifferenceEntry (ψ d : ℤ → ℂ) (n m : ℤ) :
    (((n - m : ℤ) : ℂ)) * dividedDifferenceEntry ψ d n m = ψ n - ψ m := by
  by_cases h : n = m
  · subst m
    simp [dividedDifferenceEntry]
  · rw [dividedDifferenceEntry_of_ne ψ d h]
    have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr h
    have hnmC : (((n - m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hnmZ
    field_simp [hnmC]

/-- Centered finite divided-difference matrix. -/
def dividedDifferenceMatrix (ψ d : ℤ → ℂ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j => dividedDifferenceEntry ψ d (centeredIndex N i) (centeredIndex N j)

/-- Source-value vector on the centered Fourier grid. -/
def dividedDifferenceVector (ψ : ℤ → ℂ) (N : ℕ) : Fin (2 * N + 1) → ℂ :=
  fun i => ψ (centeredIndex N i)

@[simp] theorem dividedDifferenceMatrix_apply (ψ d : ℤ → ℂ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    dividedDifferenceMatrix ψ d N i j =
      dividedDifferenceEntry ψ d (centeredIndex N i) (centeredIndex N j) := rfl

/-- Every centered divided-difference matrix has the universal rank-two
commutator form `ψ 1ᵀ - 1 ψᵀ`. -/
theorem dividedDifferenceMatrix_displacement (ψ d : ℤ → ℂ) (N : ℕ) :
    indexMatrix N * dividedDifferenceMatrix ψ d N
        - dividedDifferenceMatrix ψ d N * indexMatrix N =
      vecMulVec (dividedDifferenceVector ψ N) (fun _ => 1)
        - vecMulVec (fun _ => 1) (dividedDifferenceVector ψ N) := by
  ext i j
  change
    (indexMatrix N * dividedDifferenceMatrix ψ d N) i j -
        (dividedDifferenceMatrix ψ d N * indexMatrix N) i j =
      vecMulVec (dividedDifferenceVector ψ N) (fun _ => 1) i j -
        vecMulVec (fun _ => 1) (dividedDifferenceVector ψ N) i j
  simp only [indexMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    dividedDifferenceMatrix_apply, dividedDifferenceVector, Matrix.vecMulVec_apply,
    mul_one, one_mul]
  have h := sub_mul_dividedDifferenceEntry ψ d (centeredIndex N i) (centeredIndex N j)
  push_cast at h
  linear_combination h

/-- Generic displacement-rank bound for the entire divided-difference class. -/
theorem rank_dividedDifferenceMatrix_displacement_le_two (ψ d : ℤ → ℂ) (N : ℕ) :
    (indexMatrix N * dividedDifferenceMatrix ψ d N
      - dividedDifferenceMatrix ψ d N * indexMatrix N).rank ≤ 2 := by
  rw [dividedDifferenceMatrix_displacement]
  exact Zeta23.ExceptionalZero.rank_vecMulVec_sub_le_two _ _

/-- Changing only the diagonal convention does not change the displacement. -/
theorem dividedDifferenceMatrix_displacement_independent_of_diagonal
    (ψ d₁ d₂ : ℤ → ℂ) (N : ℕ) :
    indexMatrix N * dividedDifferenceMatrix ψ d₁ N
        - dividedDifferenceMatrix ψ d₁ N * indexMatrix N =
      indexMatrix N * dividedDifferenceMatrix ψ d₂ N
        - dividedDifferenceMatrix ψ d₂ N * indexMatrix N := by
  rw [dividedDifferenceMatrix_displacement, dividedDifferenceMatrix_displacement]

end Zeta23.CCM
