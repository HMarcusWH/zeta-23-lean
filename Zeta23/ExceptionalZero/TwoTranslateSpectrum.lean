import Zeta23.ExceptionalZero.TwoTranslateWeil
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open scoped ComplexConjugate

/-!
# X0: exact 2x2 two-translate spectrum

This file closes the finite algebraic tail of X0.  It packages the diagonal Weil
value and the relative-translation correlation into the explicit Hermitian 2x2
matrix from the active handover and computes its characteristic roots exactly.

No positivity claim is made here.
-/

/-- The complete two-translate Weil matrix.  The full zero population is already
inside each entry through `ZeroConfig.W`. -/
def twoTranslateWeilMatrix
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Z.W f f, (starRingEnd ℂ) (weilRelativeCorrelation Z f t);
     weilRelativeCorrelation Z f t, Z.W f f]

/-- Entrywise Hermitian symmetry of the explicit two-translate matrix. -/
theorem twoTranslateWeilMatrix_star_apply
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) (i j : Fin 2) :
    (starRingEnd ℂ) (twoTranslateWeilMatrix Z f t i j) =
      twoTranslateWeilMatrix Z f t j i := by
  fin_cases i <;> fin_cases j <;>
    simp [twoTranslateWeilMatrix, W_self_star]

/-- The characteristic determinant factors at the two real spectral offsets.
This is the elementary 2x2 computation behind `d ± |C_f(t)|`. -/
theorem twoTranslateWeilMatrix_det_sub_smul_one_factor
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) (λ : ℂ) :
    Matrix.det
        (twoTranslateWeilMatrix Z f t -
          λ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((Z.W f f - λ) - (‖weilRelativeCorrelation Z f t‖ : ℂ)) *
        ((Z.W f f - λ) + (‖weilRelativeCorrelation Z f t‖ : ℂ)) := by
  rw [Matrix.det_fin_two]
  simp [twoTranslateWeilMatrix]
  rw [← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Exact characteristic spectrum of the two-translate matrix:
`λ` is a characteristic root iff `λ = d + |C_f(t)|` or `λ = d - |C_f(t)|`. -/
theorem twoTranslateWeilMatrix_eigenvalue_iff
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) (λ : ℂ) :
    Matrix.det
          (twoTranslateWeilMatrix Z f t -
            λ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 ↔
      λ = Z.W f f + (‖weilRelativeCorrelation Z f t‖ : ℂ) ∨
        λ = Z.W f f - (‖weilRelativeCorrelation Z f t‖ : ℂ) := by
  rw [twoTranslateWeilMatrix_det_sub_smul_one_factor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hminus | hplus
    · right
      linear_combination -hminus
    · left
      linear_combination -hplus
  · rintro (rfl | rfl) <;> ring

/-- The upper spectral value is always a characteristic root. -/
theorem twoTranslateWeilMatrix_eigenvalue_plus
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) :
    Matrix.det
        (twoTranslateWeilMatrix Z f t -
          (Z.W f f + (‖weilRelativeCorrelation Z f t‖ : ℂ)) •
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  exact (twoTranslateWeilMatrix_eigenvalue_iff Z f t _).2 (Or.inl rfl)

/-- The lower spectral value is always a characteristic root.  X3 will target
strict negativity of this value, but no such claim is made in X0. -/
theorem twoTranslateWeilMatrix_eigenvalue_minus
    (Z : ZeroConfig) (f : ℝ → ℂ) (t : ℝ) :
    Matrix.det
        (twoTranslateWeilMatrix Z f t -
          (Z.W f f - (‖weilRelativeCorrelation Z f t‖ : ℂ)) •
            (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  exact (twoTranslateWeilMatrix_eigenvalue_iff Z f t _).2 (Or.inr rfl)

#print axioms Zeta23.ExceptionalZero.twoTranslateWeilMatrix_star_apply
#print axioms Zeta23.ExceptionalZero.twoTranslateWeilMatrix_eigenvalue_iff

end Zeta23.ExceptionalZero
