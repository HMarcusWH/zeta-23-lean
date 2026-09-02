import Zeta23.CCM.ConstrainedEuclideanSector
import Zeta23.ExceptionalZero.ConstrainedFiniteObstruction

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-!
# K0-F1E: Euclidean constrained negative obstruction

This module transports the already-proved F1/#96 negative constrained witness
into the actual Euclidean/PiLp_2 Hilbert carrier used by finite-dimensional
spectral theory.

It also theorem-locks the exact mode floor N >= 2.

No orthogonal compression, Rayleigh minimizer/eigenvalue theorem, positivity
theorem, or RH claim is asserted here.
-/

/-- The nonzero constrained F1 witness cannot occur at N=1. -/
theorem
    exists_two_le_N_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 2 ≤ N ∧
        ∃ u : Fin (2 * N + 1) → ℂ,
          u ≠ 0 ∧
          u ∈ Zeta23.CCM.boundaryFlatSubspace N ∧
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨L, hL, N, hN, u, hne, hmem, hneg⟩ :=
    exists_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hoff
  have hN2 :=
    Zeta23.CCM.two_le_of_ne_zero_mem_boundaryFlatSubspace
      hN hmem hne
  exact ⟨L, hL, N, hN2, u, hne, hmem, hneg⟩

/-- **Euclidean constrained F1 obstruction.**

Every hypothetical off-critical-line zeta zero forces a nonzero vector in the
exact Euclidean boundary-flat sector whose canonical symmetric operator has
strictly negative real inner-self value. -/
theorem
    exists_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 2 ≤ N ∧
        ∃ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ≠ 0 ∧
          x ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace N ∧
          Complex.re (inner ℂ
            ((Zeta23.CCM.canonicalSourceMatrix L N).toEuclideanLin x)
            x) < 0 := by
  obtain ⟨L, hL, N, hN2, u, hne, hmem, hneg⟩ :=
    exists_two_le_N_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hoff
  let e :=
    EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ
  let x : EuclideanSpace ℂ (Fin (2 * N + 1)) := e.symm u
  have hxne : x ≠ 0 := by
    intro hx
    apply hne
    have hxe : e x = e 0 := congrArg e hx
    simpa [x, e] using hxe
  have hxmem :
      x ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace N := by
    rw [Zeta23.CCM.mem_euclideanBoundaryFlatSubspace_iff]
    simpa [x, e] using hmem
  have hxneg :
      Complex.re (inner ℂ
        ((Zeta23.CCM.canonicalSourceMatrix L N).toEuclideanLin x)
        x) < 0 := by
    calc
      Complex.re (inner ℂ
          ((Zeta23.CCM.canonicalSourceMatrix L N).toEuclideanLin x)
          x) =
          (Zeta23.CCM.quadraticForm
            (Zeta23.CCM.canonicalSourceMatrix L N) u).re := by
              symm
              simpa [x, e] using
                (Zeta23.CCM.quadraticForm_re_eq_re_inner_apply_self
                  (Zeta23.CCM.canonicalSourceMatrix L N) x)
      _ < 0 := hneg
  exact ⟨L, hL, N, hN2, x, hxne, hxmem, hxneg⟩

/-- Existential wrapper for the Euclidean constrained obstruction. -/
theorem
    exists_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N : ℕ, 2 ≤ N ∧
        ∃ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
          x ≠ 0 ∧
          x ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace N ∧
          Complex.re (inner ℂ
            ((Zeta23.CCM.canonicalSourceMatrix L N).toEuclideanLin x)
            x) < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_offLine_zero
      ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_two_le_N_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_exists_offLine_zero
