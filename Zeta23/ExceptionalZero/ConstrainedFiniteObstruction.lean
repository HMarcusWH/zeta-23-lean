import Zeta23.CCM.ConstrainedCanonicalSector
import Zeta23.ExceptionalZero.FiniteNegativeObstruction
import Mathlib.Analysis.Normed.Module.RCLike.Basic

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex
open scoped BigOperators ComplexConjugate

/-!
# Post-F1 constrained finite obstruction

F1 already proves that every hypothetical off-critical-line zeta zero forces a
negative quadratic direction of one finite `canonicalSourceMatrix` satisfying
the three exact boundary-flat moments.

This module repackages that witness inside the actual complex subspace used by
finite-dimensional linear algebra, proves it is nonzero, and normalizes it to
unit norm without changing the strict sign.

No constrained minimizer/eigenvector theorem, positivity theorem, or RH claim is
asserted here.
-/

/-- A strictly negative quadratic value cannot occur at the zero vector. -/
theorem ne_zero_of_quadraticForm_re_neg
    {ι : Type*}
    [Fintype ι]
    (A : Matrix ι ι ℂ)
    (u : ι → ℂ)
    (hneg : (Zeta23.CCM.quadraticForm A u).re < 0) :
    u ≠ 0 := by
  intro hu
  subst u
  simpa using hneg

/-- F1 restated in the complex subspace that exactly packages the three
boundary-flat centered moments. -/
theorem
    exists_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          u ∈ Zeta23.CCM.boundaryFlatSubspace N ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨L, hL, N, hN, u, hflat, hneg⟩ :=
    exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hoff
  exact ⟨L, hL, N, hN, u,
    (Zeta23.CCM.mem_boundaryFlatSubspace_iff N u).2 hflat,
    hneg⟩

/-- Existential wrapper for the constrained-subspace F1 statement. -/
theorem
    exists_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          u ∈ Zeta23.CCM.boundaryFlatSubspace N ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hρ₀

/-- Strictly negative canonical constrained witnesses are nonzero. -/
theorem
    exists_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          u ≠ 0 ∧
          u ∈ Zeta23.CCM.boundaryFlatSubspace N ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨L, hL, N, hN, u, hmem, hneg⟩ :=
    exists_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hoff
  have hne :=
    ne_zero_of_quadraticForm_re_neg
      (Zeta23.CCM.canonicalSourceMatrix L N) u hneg
  exact ⟨L, hL, N, hN, u, hne, hmem, hneg⟩

/-- Positive real normalization preserves strict negativity of the canonical
quadratic form. -/
theorem quadraticForm_inv_norm_smul_re_neg
    {ι : Type*}
    [Fintype ι]
    (A : Matrix ι ι ℂ)
    (u : ι → ℂ)
    (hu : u ≠ 0)
    (hneg : (Zeta23.CCM.quadraticForm A u).re < 0) :
    (Zeta23.CCM.quadraticForm A
      ((‖u‖⁻¹ : ℂ) • u)).re < 0 := by
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hinv : 0 < ‖u‖⁻¹ := inv_pos.mpr hnorm
  rw [Zeta23.CCM.quadraticForm_smul]
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg (mul_pos hinv hinv) hneg

/-- **Normalized constrained F1 obstruction.**

Every hypothetical off-critical-line zeta zero forces a unit-norm vector in the
exact boundary-flat subspace with strictly negative canonical quadratic value. -/
theorem
    exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          u ∈ Zeta23.CCM.boundaryFlatSubspace N ∧
          ‖u‖ = 1 ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨L, hL, N, hN, u, hne, hmem, hneg⟩ :=
    exists_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hoff
  let v : Fin (2 * N + 1) → ℂ := (‖u‖⁻¹ : ℂ) • u
  have hv_mem : v ∈ Zeta23.CCM.boundaryFlatSubspace N := by
    exact (Zeta23.CCM.boundaryFlatSubspace N).smul_mem _ hmem
  have hv_norm : ‖v‖ = 1 := by
    simpa [v] using (norm_smul_inv_norm (𝕜 := ℂ) hne)
  have hv_neg :
      (Zeta23.CCM.quadraticForm
        (Zeta23.CCM.canonicalSourceMatrix L N) v).re < 0 := by
    simpa [v] using
      quadraticForm_inv_norm_smul_re_neg
        (Zeta23.CCM.canonicalSourceMatrix L N) u hne hneg
  exact ⟨L, hL, N, hN, v, hv_mem, hv_norm, hv_neg⟩

/-- Existential normalized F1 wrapper. -/
theorem
    exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          u ∈ Zeta23.CCM.boundaryFlatSubspace N ∧
          ‖u‖ = 1 ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.ne_zero_of_quadraticForm_re_neg
#print axioms Zeta23.ExceptionalZero.exists_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.quadraticForm_inv_norm_smul_re_neg
#print axioms Zeta23.ExceptionalZero.exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_exists_offLine_zero
