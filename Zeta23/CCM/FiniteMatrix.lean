import Zeta23.CCM.Components
import Mathlib.Data.Matrix.Mul

noncomputable section

namespace Zeta23.CCM

open Matrix

/-- Integer Fourier index represented by `i : Fin (2N+1)`, centered at zero. -/
def centeredIndex (N : ℕ) (i : Fin (2 * N + 1)) : ℤ :=
  (i.1 : ℤ) - (N : ℤ)

/-- Canonical finite CCM matrix on Fourier indices `-N,...,N`. -/
def finiteMatrix (L : ℝ) (N : ℕ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j => (entry (centeredIndex N i) (centeredIndex N j) L : ℂ)

/-- Diagonal Fourier-index operator used by the displacement identity. -/
def indexMatrix (N : ℕ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  diagonal fun i => ((centeredIndex N i : ℤ) : ℂ)

@[simp] theorem finiteMatrix_apply (L : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    finiteMatrix L N i j = (entry (centeredIndex N i) (centeredIndex N j) L : ℂ) := rfl

@[simp] theorem indexMatrix_apply (N : ℕ) (i j : Fin (2 * N + 1)) :
    indexMatrix N i j = if i = j then ((centeredIndex N i : ℤ) : ℂ) else 0 := by
  simp [indexMatrix]

end Zeta23.CCM
