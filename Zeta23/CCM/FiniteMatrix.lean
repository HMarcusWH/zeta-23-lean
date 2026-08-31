import Zeta23.CCM.Components
import Mathlib.Data.Matrix.Mul

noncomputable section

namespace Zeta23.CCM

open Matrix

/-- Integer Fourier index represented by `i : Fin (2N+1)`, centered at zero. -/
def centeredIndex (N : ℕ) (i : Fin (2 * N + 1)) : ℤ :=
  (i.1 : ℤ) - (N : ℤ)

/-- Historical printed-normalization finite matrix on Fourier indices `-N,...,N`.  Kept unchanged for theorem history; the canonical direct-source matrix is `canonicalSourceMatrix = cutoffFreeMatrix`. -/
def finiteMatrix (L : ℝ) (N : ℕ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j => (entry (centeredIndex N i) (centeredIndex N j) L : ℂ)

/-- Historical lambda wrapper for the printed-normalization matrix, with `L = 2 * log(lam)`.  Do not identify this directly with the ambient external `QW_lambda` restriction. -/
def finiteMatrixOfLambda (lam : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  finiteMatrix (2 * Real.log lam) N

/-- Diagonal Fourier-index operator used by the displacement identity. -/
def indexMatrix (N : ℕ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  diagonal fun i => ((centeredIndex N i : ℤ) : ℂ)

@[simp] theorem finiteMatrix_apply (L : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    finiteMatrix L N i j = (entry (centeredIndex N i) (centeredIndex N j) L : ℂ) := rfl

@[simp] theorem finiteMatrixOfLambda_apply (lam : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    finiteMatrixOfLambda lam N i j =
      (entry (centeredIndex N i) (centeredIndex N j) (2 * Real.log lam) : ℂ) := rfl

@[simp] theorem indexMatrix_apply (N : ℕ) (i j : Fin (2 * N + 1)) :
    indexMatrix N i j = if i = j then ((centeredIndex N i : ℤ) : ℂ) else 0 := by
  by_cases h : i = j
  · subst j
    simp [indexMatrix]
  · simp [indexMatrix, h]

end Zeta23.CCM
