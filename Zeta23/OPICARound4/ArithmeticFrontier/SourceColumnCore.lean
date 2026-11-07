import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The finite source-core consumer (C4)

Let `H` be self-adjoint on a physical inner product space and let `S` be a
core subspace, for instance the span of selected source columns. The leakage
`η` bounds the operator norm of `(I - P) H`; it is tested against the whole
orthogonal complement, so the entire discarded-sector coupling is retained.
The Frobenius residual `‖(I - P) H‖_F` dominates it.

If `η ≤ ε/4` and the core form satisfies `D_I + (11ε/12) G_I ≥ 0`, then
`H + ε I ≥ 0`. The constant comes from `η²/(ε - η) ≤ ε/12`. The column form
keeps the nonorthogonal physical Gram `G_I = C* C`.

This is a sound consumer. It does not prove its signed-core premise, and no
native source estimate follows from it.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Leakage out of the core, measured against every orthogonal direction. -/
def CoreLeakageBound (H : E →ₗ[ℂ] E) (S : Submodule ℂ E) (η : ℝ) : Prop :=
  ∀ (x q : E), q ∈ Sᗮ → ‖inner ℂ (H x) q‖ ≤ η * ‖x‖ * ‖q‖

private theorem re_inner_swap' (x y : E) : (inner ℂ x y).re = (inner ℂ y x).re := by
  rw [← inner_conj_symm x y, Complex.conj_re]

private theorem core_quadratic_nonneg {ε η s t : ℝ} (hη : 0 ≤ η) (hηε : η ≤ ε / 4) :
    0 ≤ ε / 12 * s ^ 2 - 2 * η * s * t + (ε - η) * t ^ 2 := by
  have hε : 0 ≤ ε := by linarith
  rcases hε.lt_or_eq with hε | hε
  · have h4 : 0 ≤ ε - 4 * η := by linarith
    have h3 : 0 ≤ ε + 3 * η := by linarith
    have key : 0 ≤ 12 * ε * (ε / 12 * s ^ 2 - 2 * η * s * t + (ε - η) * t ^ 2) := by
      nlinarith [sq_nonneg (ε * s - 12 * η * t), mul_nonneg (mul_nonneg h4 h3) (sq_nonneg t)]
    by_contra hneg
    have hneg : ε / 12 * s ^ 2 - 2 * η * s * t + (ε - η) * t ^ 2 < 0 := lt_of_not_ge hneg
    have := mul_neg_of_pos_of_neg (by positivity : (0 : ℝ) < 12 * ε) hneg
    linarith
  · have hη0 : η = 0 := by linarith
    subst hη0
    rw [← hε]
    ring_nf
    rfl

private theorem re_lower_of_leak {x q : E} {η : ℝ}
    (h : ‖inner ℂ x q‖ ≤ η) : -η ≤ (inner ℂ x q).re := by
  have h1 := (abs_le.mp ((Complex.abs_re_le_norm (inner ℂ x q)).trans h)).1
  linarith

/-- Exact orthogonal splitting of a self-adjoint energy. -/
theorem selfAdjoint_energy_split (H : E →ₗ[ℂ] E)
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y)) (p q : E) :
    (inner ℂ (H (p + q)) (p + q)).re =
      (inner ℂ (H p) p).re + 2 * (inner ℂ (H p) q).re + (inner ℂ (H q) q).re := by
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
  have : (inner ℂ (H q) p).re = (inner ℂ (H p) q).re := by
    rw [hH, re_inner_swap']
  linarith

/-- **Source-core consumer (C4).** -/
theorem core_shift_certificate (H : E →ₗ[ℂ] E) (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y)) {ε η : ℝ}
    (hη : 0 ≤ η) (hηε : η ≤ ε / 4) (hleak : CoreLeakageBound H S η)
    (hcore : ∀ p ∈ S, -(11 * ε / 12) * ‖p‖ ^ 2 ≤ (inner ℂ (H p) p).re) :
    ∀ v : E, -ε * ‖v‖ ^ 2 ≤ (inner ℂ (H v) v).re := by
  intro v
  obtain ⟨p, hp, q, hq, rfl⟩ := S.exists_add_mem_mem_orthogonal v
  have hpq : inner ℂ p q = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hpq
  have hnorm : ‖p + q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by nlinarith [hn]
  rw [selfAdjoint_energy_split H hH p q, hnorm]
  have h1 := re_lower_of_leak (hleak p q hq)
  have h2 := re_lower_of_leak (hleak q q hq)
  have h3 := hcore p hp
  have hQ := core_quadratic_nonneg (s := ‖p‖) (t := ‖q‖) hη hηε
  nlinarith

/-- Column form: `D_I + (11ε/12) G_I ≥ 0` in selected-column coordinates, with
the nonorthogonal physical Gram `G_I c = ‖C c‖²`, and leakage out of the
column span, imply the physical shift `H + ε I ≥ 0`. -/
theorem core_shift_certificate_of_columns [FiniteDimensional ℂ E] {V : Type*}
    [AddCommGroup V] [Module ℂ V] (H : E →ₗ[ℂ] E) (Ccol : V →ₗ[ℂ] E)
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y)) {ε η : ℝ}
    (hη : 0 ≤ η) (hηε : η ≤ ε / 4) (hleak : CoreLeakageBound H (LinearMap.range Ccol) η)
    (hcols : ∀ c : V, -(11 * ε / 12) * ‖Ccol c‖ ^ 2 ≤ (inner ℂ (H (Ccol c)) (Ccol c)).re) :
    ∀ v : E, -ε * ‖v‖ ^ 2 ≤ (inner ℂ (H v) v).re := by
  apply core_shift_certificate H (LinearMap.range Ccol) hH hη hηε hleak
  rintro p ⟨c, rfl⟩
  exact hcols c

/-- **Negative-witness transport (E2).** Paid compression keeps a fixed negative
margin on the projected component of the same trial, with the conservative
constant `3η`. The projection is not identified with a ground eigenvector. -/
theorem core_witness_transport (H : E →ₗ[ℂ] E) (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y)) {η d : ℝ}
    (hη : 0 ≤ η) (hηd : 3 * η < d) (hleak : CoreLeakageBound H S η) (x : E)
    (hneg : (inner ℂ (H x) x).re < -d * ‖x‖ ^ 2) :
    ∃ p ∈ S, x - p ∈ Sᗮ ∧ p ≠ 0 ∧ (inner ℂ (H p) p).re < -(d - 3 * η) * ‖p‖ ^ 2 := by
  obtain ⟨p, hp, q, hq, rfl⟩ := S.exists_add_mem_mem_orthogonal x
  have hpq : inner ℂ p q = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hpq
  have hnorm : ‖p + q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by nlinarith [hn]
  rw [selfAdjoint_energy_split H hH p q, hnorm] at hneg
  have h1 := re_lower_of_leak (hleak p q hq)
  have h2 := re_lower_of_leak (hleak q q hq)
  have hcross : 2 * (η * ‖p‖ * ‖q‖) ≤ η * ‖p‖ ^ 2 + η * ‖q‖ ^ 2 := by
    nlinarith [mul_nonneg hη (sq_nonneg (‖p‖ - ‖q‖))]
  have hrest : 0 ≤ (d - 2 * η) * ‖q‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hpp : 0 ≤ 2 * η * ‖p‖ ^ 2 := by positivity
  have hmain : (inner ℂ (H p) p).re < -(d - 3 * η) * ‖p‖ ^ 2 := by
    nlinarith
  refine ⟨p, hp, by simpa using hq, ?_, hmain⟩
  rintro rfl
  simp at hmain

end Zeta23.OPICARound4.ArithmeticFrontier
