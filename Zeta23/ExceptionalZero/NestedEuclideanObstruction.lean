import Zeta23.CCM.NestedFinite
import Zeta23.ExceptionalZero.EuclideanConstrainedObstruction

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-!
# N-FLOW-B: persistent Euclidean constrained negative obstruction

The PR #98 obstruction produces one negative constrained Euclidean direction.
Exact centered finite nesting transports that same direction, at the same
physical aperture, to every larger centered truncation.

No compressed eigenmode, first bad truncation, parity sector, positivity
theorem, or RH claim is made here.
-/

theorem negativeEuclideanConstrained_persists_of_le
    {L : ℝ} (hL : 0 < L)
    {N M : ℕ} (hNM : N ≤ M)
    {x : EuclideanSpace ℂ (Fin (2 * N + 1))}
    (hxne : x ≠ 0)
    (hxmem : x ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace N)
    (hxneg :
      Complex.re (inner ℂ
        ((Zeta23.CCM.canonicalSourceMatrix L N).toEuclideanLin x)
        x) < 0) :
    let y := Zeta23.CCM.euclideanCenteredZeroExtend hNM x
    y ≠ 0 ∧
      y ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace M ∧
      Complex.re (inner ℂ
        ((Zeta23.CCM.canonicalSourceMatrix L M).toEuclideanLin y)
        y) < 0 := by
  let y := Zeta23.CCM.euclideanCenteredZeroExtend hNM x
  have hyne : y ≠ 0 := by
    intro hy
    apply hxne
    apply (Zeta23.CCM.euclideanCenteredZeroExtend hNM).injective
    simpa [y] using hy
  have hymem :
      y ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace M := by
    exact
      Zeta23.CCM.euclideanCenteredZeroExtend_mem_euclideanBoundaryFlatSubspace
        hNM hxmem
  have hyneg :
      Complex.re (inner ℂ
        ((Zeta23.CCM.canonicalSourceMatrix L M).toEuclideanLin y)
        y) < 0 := by
    rw [Zeta23.CCM.re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
      hL hNM x]
    exact hxneg
  exact ⟨hyne, hymem, hyneg⟩

theorem
    exists_fixedAperture_forall_ge_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧
        ∀ M : ℕ, N₀ ≤ M →
          ∃ x : EuclideanSpace ℂ (Fin (2 * M + 1)),
            x ≠ 0 ∧
            x ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace M ∧
            Complex.re (inner ℂ
              ((Zeta23.CCM.canonicalSourceMatrix L M).toEuclideanLin x)
              x) < 0 := by
  obtain ⟨L, hL, N₀, hN₀, x, hxne, hxmem, hxneg⟩ :=
    exists_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_offLine_zero
      ρ₀ hoff
  refine ⟨L, hL, N₀, hN₀, ?_⟩
  intro M hNM
  let y := Zeta23.CCM.euclideanCenteredZeroExtend hNM x
  have hp :=
    negativeEuclideanConstrained_persists_of_le
      hL hNM hxne hxmem hxneg
  exact ⟨y, hp.1, hp.2.1, hp.2.2⟩

theorem
    exists_fixedAperture_forall_ge_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧
        ∀ M : ℕ, N₀ ≤ M →
          ∃ x : EuclideanSpace ℂ (Fin (2 * M + 1)),
            x ≠ 0 ∧
            x ∈ Zeta23.CCM.euclideanBoundaryFlatSubspace M ∧
            Complex.re (inner ℂ
              ((Zeta23.CCM.canonicalSourceMatrix L M).toEuclideanLin x)
              x) < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_fixedAperture_forall_ge_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_offLine_zero
      ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.negativeEuclideanConstrained_persists_of_le
#print axioms Zeta23.ExceptionalZero.exists_fixedAperture_forall_ge_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_fixedAperture_forall_ge_ne_zero_mem_euclideanBoundaryFlatSubspace_negativeCanonicalInnerSelf_of_exists_offLine_zero
