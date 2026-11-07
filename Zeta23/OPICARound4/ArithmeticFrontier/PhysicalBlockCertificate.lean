import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Complete inverse-residual block certificates

For a Hermitian block `B = [[D, C], [C*, A]]` with `A ≥ a > 0` and any trial
inverse action `X`, put `R = C* - A X`. The exact identity

`D - C A⁻¹ C* = D - C X - X* C* + X* A X - R* A⁻¹ R`

holds as quadratic forms, and `R* A⁻¹ R ≤ a⁻¹ R* R`. Hence the certificate
`D - C X - X* C* + X* A X - a⁻¹ R* R ≥ 0` proves `B ≥ 0` with the entire
coupling retained. No global upper bound on `A`, constant unshifted gap or
fixed approximation degree is required. Physical-metric tolerances are obtained
by applying the same theorem to `D + ε G_E` and `A + ε G_F`; the identity metric
is never substituted for a nonunitary Gram.

This is finite linear algebra. It certifies nothing about the native source
until actual enclosed data and a proved enclosure bridge are supplied.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The complete real block energy of `[[D, C], [C*, A]]` at `(u, w)`. -/
def blockEnergy (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (A : F →ₗ[ℂ] F) (u : E) (w : F) : ℝ :=
  (inner ℂ (D u) u).re + 2 * (inner ℂ (C w) u).re + (inner ℂ (A w) w).re

/-- The corrected Schur form `D - C X - X* C* + X* A X` at `u`. -/
def correctedSchurForm (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (A : F →ₗ[ℂ] F)
    (X : E →ₗ[ℂ] F) (u : E) : ℝ :=
  (inner ℂ (D u) u).re - 2 * (inner ℂ (C (X u)) u).re + (inner ℂ (A (X u)) (X u)).re

/-- The inverse residual `R u = C* u - A X u`. -/
def inverseResidual (Cadj : E →ₗ[ℂ] F) (A : F →ₗ[ℂ] F) (X : E →ₗ[ℂ] F) (u : E) : F :=
  Cadj u - A (X u)

private theorem re_inner_swap {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (x y : G) : (inner ℂ x y).re = (inner ℂ y x).re := by
  rw [← inner_conj_symm x y, Complex.conj_re]

/-- Exact rewriting of the complete block energy around the trial inverse action. -/
theorem blockEnergy_eq_residual_form (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (Cadj : E →ₗ[ℂ] F)
    (A : F →ₗ[ℂ] F) (X : E →ₗ[ℂ] F)
    (hA : ∀ z z' : F, inner ℂ (A z) z' = inner ℂ z (A z'))
    (hC : ∀ (u : E) (w : F), inner ℂ (C w) u = inner ℂ w (Cadj u)) (u : E) (w : F) :
    blockEnergy D C A u w =
      correctedSchurForm D C A X u +
        2 * (inner ℂ (w + X u) (inverseResidual Cadj A X u)).re +
        (inner ℂ (A (w + X u)) (w + X u)).re := by
  unfold blockEnergy correctedSchurForm inverseResidual
  have h1 := hC u w
  have h2 := hC u (X u)
  have h3 : (inner ℂ (A (X u)) w).re = (inner ℂ (A w) (X u)).re := by
    rw [hA, re_inner_swap]
  have h4 : (inner ℂ w (A (X u))).re = (inner ℂ (A w) (X u)).re := by
    rw [← hA]
  have h5 : (inner ℂ (X u) (A (X u))).re = (inner ℂ (A (X u)) (X u)).re := by
    rw [← hA]
  simp only [map_add, inner_add_left, inner_add_right, inner_sub_right, Complex.add_re,
    Complex.sub_re]
  rw [← h1, ← h2]
  linarith

/-- **Inverse-residual certificate soundness.** With `A ≥ a > 0`, the corrected
Schur form dominating `a⁻¹ ‖R u‖²` proves the complete block is nonnegative. -/
theorem blockEnergy_nonneg_of_inverse_residual_certificate
    (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (Cadj : E →ₗ[ℂ] F) (A : F →ₗ[ℂ] F) (X : E →ₗ[ℂ] F)
    {a : ℝ} (ha : 0 < a)
    (hA : ∀ z z' : F, inner ℂ (A z) z' = inner ℂ z (A z'))
    (hApos : ∀ z : F, a * ‖z‖ ^ 2 ≤ (inner ℂ (A z) z).re)
    (hC : ∀ (u : E) (w : F), inner ℂ (C w) u = inner ℂ w (Cadj u))
    (hcert : ∀ u : E, a⁻¹ * ‖inverseResidual Cadj A X u‖ ^ 2 ≤ correctedSchurForm D C A X u)
    (u : E) (w : F) : 0 ≤ blockEnergy D C A u w := by
  rw [blockEnergy_eq_residual_form D C Cadj A X hA hC u w]
  set z := w + X u
  set r := inverseResidual Cadj A X u
  have hcs : -(‖z‖ * ‖r‖) ≤ (inner ℂ z r).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm (inner ℂ z r)).trans (norm_inner_le_norm z r))).1
    linarith
  have hz := hApos z
  have hs := hcert u
  have hsq : 0 ≤ a⁻¹ * (a * ‖z‖ - ‖r‖) ^ 2 := by positivity
  have hexp : a⁻¹ * (a * ‖z‖ - ‖r‖) ^ 2 = a * ‖z‖ ^ 2 - 2 * (‖z‖ * ‖r‖) + a⁻¹ * ‖r‖ ^ 2 := by
    field_simp
    ring
  linarith

/-- The exact identity `D - C A⁻¹ C* = D - CX - X*C* + X*AX - R* A⁻¹ R` as forms. -/
theorem schur_inverse_residual_identity (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (Cadj : E →ₗ[ℂ] F)
    (A Ainv : F →ₗ[ℂ] F) (X : E →ₗ[ℂ] F)
    (hA : ∀ z z' : F, inner ℂ (A z) z' = inner ℂ z (A z'))
    (hleft : ∀ z : F, Ainv (A z) = z) (hright : ∀ z : F, A (Ainv z) = z)
    (hC : ∀ (u : E) (w : F), inner ℂ (C w) u = inner ℂ w (Cadj u)) (u : E) :
    (inner ℂ (D u) u).re - (inner ℂ (C (Ainv (Cadj u))) u).re =
      correctedSchurForm D C A X u -
        (inner ℂ (Ainv (inverseResidual Cadj A X u)) (inverseResidual Cadj A X u)).re := by
  unfold correctedSchurForm inverseResidual
  have h1 := hC u (Ainv (Cadj u))
  have h2 := hC u (X u)
  have h3 : (inner ℂ (Ainv (Cadj u)) (A (X u))).re = (inner ℂ (X u) (Cadj u)).re := by
    rw [← hA, hright, re_inner_swap]
  have h4 : (inner ℂ (X u) (A (X u))).re = (inner ℂ (A (X u)) (X u)).re := by
    rw [← hA]
  simp only [map_sub, hleft, inner_sub_left, inner_sub_right, Complex.sub_re]
  rw [h1, h2]
  linarith

/-- The scalar inverse-gap surrogate is exactly the `X = 0` special case. -/
theorem blockEnergy_nonneg_of_scalar_gap
    (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (Cadj : E →ₗ[ℂ] F) (A : F →ₗ[ℂ] F)
    {a : ℝ} (ha : 0 < a)
    (hA : ∀ z z' : F, inner ℂ (A z) z' = inner ℂ z (A z'))
    (hApos : ∀ z : F, a * ‖z‖ ^ 2 ≤ (inner ℂ (A z) z).re)
    (hC : ∀ (u : E) (w : F), inner ℂ (C w) u = inner ℂ w (Cadj u))
    (hcert : ∀ u : E, a⁻¹ * ‖Cadj u‖ ^ 2 ≤ (inner ℂ (D u) u).re)
    (u : E) (w : F) : 0 ≤ blockEnergy D C A u w := by
  apply blockEnergy_nonneg_of_inverse_residual_certificate D C Cadj A 0 ha hA hApos hC _ u w
  intro v
  simpa [correctedSchurForm, inverseResidual] using hcert v

/-- Tolerance monotonicity for a nonnegative physical metric form. -/
theorem shifted_form_mono {V : Type*} (q g : V → ℝ) (hg : ∀ x, 0 ≤ g x) {ε ε' : ℝ}
    (hε : ε ≤ ε') (h : ∀ x, 0 ≤ q x + ε * g x) : ∀ x, 0 ≤ q x + ε' * g x := by
  intro x
  have := h x
  have := hg x
  nlinarith

end Zeta23.OPICARound4.ArithmeticFrontier
