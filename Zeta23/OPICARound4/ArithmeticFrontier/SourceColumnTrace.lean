import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel

/-!
# Source-column Gram and trace identities (work package E, §10)

Let `H` be self-adjoint and let `S` be a column selection or any column map.
The actual source columns are `C = H S`, with physical Gram `G = Cᴴ C`. If `G`
is invertible, `P = C G⁻¹ Cᴴ` is the orthogonal projection onto the span of the
columns. This module proves

* `G = Sᴴ H² S` and `Cᴴ H C = Sᴴ H³ S` (for a coordinate selection these are
  `(H²)_II` and `(H³)_II`);
* `P` is self-adjoint and idempotent;
* the exact Frobenius identity for the discarded sector,
  `‖(1 - P) H‖²_F = tr(H²) - tr(G⁻¹ Sᴴ H⁴ S)`, written as a trace.

These are the identities that turn the C4 source-core consumer
(`core_shift_certificate_of_columns`) into a computable leakage. They do not
prove the signed-core premise or any source estimate. Numerically, the residual
should be enclosed directly when the two traces nearly cancel.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open Matrix

variable {N k : Type*} [Fintype N] [Fintype k]

omit [Fintype k] in
/-- The physical Gram of the source columns `C = H S` is `Sᴴ H² S`. -/
theorem sourceColumn_gram_eq (H : Matrix N N ℂ) (S : Matrix N k ℂ) (hH : Hᴴ = H) :
    (H * S)ᴴ * (H * S) = Sᴴ * (H * H) * S := by
  rw [conjTranspose_mul, hH]
  simp only [Matrix.mul_assoc]

omit [Fintype k] in
/-- The compressed source on the columns is `Sᴴ H³ S`. -/
theorem sourceColumn_energy_eq (H : Matrix N N ℂ) (S : Matrix N k ℂ) (hH : Hᴴ = H) :
    (H * S)ᴴ * H * (H * S) = Sᴴ * (H * H * H) * S := by
  rw [conjTranspose_mul, hH]
  simp only [Matrix.mul_assoc]

/-- The column projection `P = C G⁻¹ Cᴴ` is self-adjoint. -/
theorem columnProjection_conjTranspose [DecidableEq k] (C : Matrix N k ℂ) :
    (C * (Cᴴ * C)⁻¹ * Cᴴ)ᴴ = C * (Cᴴ * C)⁻¹ * Cᴴ := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc]

/-- The column projection is idempotent when the Gram is invertible. -/
theorem columnProjection_idempotent [DecidableEq k] (C : Matrix N k ℂ) (hG : IsUnit (Cᴴ * C).det) :
    (C * (Cᴴ * C)⁻¹ * Cᴴ) * (C * (Cᴴ * C)⁻¹ * Cᴴ) = C * (Cᴴ * C)⁻¹ * Cᴴ := by
  have h : (Cᴴ * C)⁻¹ * (Cᴴ * C) = 1 := nonsing_inv_mul _ hG
  calc (C * (Cᴴ * C)⁻¹ * Cᴴ) * (C * (Cᴴ * C)⁻¹ * Cᴴ)
      = C * (((Cᴴ * C)⁻¹ * (Cᴴ * C)) * ((Cᴴ * C)⁻¹ * Cᴴ)) := by simp only [Matrix.mul_assoc]
    _ = C * (Cᴴ * C)⁻¹ * Cᴴ := by rw [h, Matrix.one_mul, Matrix.mul_assoc]

/-- `(1 - P)ᴴ (1 - P) = 1 - P` for the column projection. -/
theorem complementProjection_sq [DecidableEq N] [DecidableEq k] (C : Matrix N k ℂ) (hG : IsUnit (Cᴴ * C).det) :
    (1 - C * (Cᴴ * C)⁻¹ * Cᴴ)ᴴ * (1 - C * (Cᴴ * C)⁻¹ * Cᴴ) = 1 - C * (Cᴴ * C)⁻¹ * Cᴴ := by
  rw [conjTranspose_sub, conjTranspose_one, columnProjection_conjTranspose]
  have hP := columnProjection_idempotent C hG
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP]
  abel

private theorem residual_gram_aux (Q H : Matrix N N ℂ) (hH : Hᴴ = H) :
    (Q * H)ᴴ * (Q * H) = H * (Qᴴ * Q) * H := by
  rw [conjTranspose_mul, hH]
  simp only [Matrix.mul_assoc]

private theorem residual_split_aux [DecidableEq N] (H : Matrix N N ℂ) (C : Matrix N k ℂ) (M : Matrix k k ℂ) :
    H * (1 - C * M * Cᴴ) * H = H * H - (H * C * M) * (Cᴴ * H) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]

private theorem residual_fourth_aux (H : Matrix N N ℂ) (S : Matrix N k ℂ) (M : Matrix k k ℂ) (hH : Hᴴ = H) :
    (H * S)ᴴ * H * (H * (H * S) * M) = (Sᴴ * (H * H * H * H) * S) * M := by
  rw [conjTranspose_mul, hH]
  simp only [Matrix.mul_assoc]

/-- **Exact discarded-sector identity.** For self-adjoint `H`, columns `C = H S` with invertible
Gram `G = Cᴴ C` and `P = C G⁻¹ Cᴴ`: `tr(((1 - P) H)ᴴ ((1 - P) H)) = tr(H²) - tr(G⁻¹ Sᴴ H⁴ S)`. -/
theorem sourceColumn_residual_trace [DecidableEq N] [DecidableEq k] (H : Matrix N N ℂ) (S : Matrix N k ℂ)
    (hH : Hᴴ = H) (hG : IsUnit ((H * S)ᴴ * (H * S)).det) :
    trace (((1 - (H * S) * ((H * S)ᴴ * (H * S))⁻¹ * (H * S)ᴴ) * H)ᴴ *
        ((1 - (H * S) * ((H * S)ᴴ * (H * S))⁻¹ * (H * S)ᴴ) * H))
      = trace (H * H) - trace (((H * S)ᴴ * (H * S))⁻¹ * (Sᴴ * (H * H * H * H) * S)) := by
  rw [residual_gram_aux _ H hH, complementProjection_sq (H * S) hG, residual_split_aux H (H * S),
    trace_sub, trace_mul_comm (H * (H * S) * ((H * S)ᴴ * (H * S))⁻¹) ((H * S)ᴴ * H),
    residual_fourth_aux H S _ hH,
    trace_mul_comm (Sᴴ * (H * H * H * H) * S) (((H * S)ᴴ * (H * S))⁻¹)]

end Zeta23.OPICARound4.ArithmeticFrontier
