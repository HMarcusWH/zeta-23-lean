import Zeta23.ExceptionalZero.ApertureFreedom
import Zeta23.CCM.CanonicalApertureContinuity

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Function MeasureTheory Real Set

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1a: fixed-cell witness persistence

This module composes the aperture freedom theorem with the fixed-cell
continuity theorem for the actual production `canonicalSourceMatrix`.

The quantifier change is the point: PR #140 allows the finite size and witness
to vary with the aperture.  After choosing one interior aperture `L₁` in one
physical cutoff cell, the particular finite size `N` and particular witness
`u` supplied at `L₁` remain strictly negative on an open neighborhood `J`
contained in that same cutoff cell.

No regular-aperture selection, determinant nonidentity, predecessor
holomorphy, positivity theorem, negative-root exclusion, or RH claim is
asserted here.
-/

/-- A hypothetical off-line zero supplies, beyond one aperture threshold, a
locally persistent fixed finite canonical negative witness at every chosen
interior aperture of every physical cutoff cell.

The same `N` and the same `u` remain negative throughout the resulting open
neighborhood `J`; only the original choice at `L₁` comes from aperture
freedom. -/
theorem
    eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ Q : ℕ, 1 ≤ Q →
        ∀ L₁ : ℝ,
          L₁ ∈ Zeta23.CCM.fixedCanonicalCutoffCell Q →
          L₀ < L₁ →
          ∃ N : ℕ, 1 ≤ N ∧
            ∃ u : Fin (2 * N + 1) → ℂ,
              Zeta23.CCM.BoundaryFlatCoefficients N u ∧
              ∃ J : Set ℝ,
                IsOpen J ∧
                L₁ ∈ J ∧
                J ⊆ Zeta23.CCM.fixedCanonicalCutoffCell Q ∧
                ∀ L ∈ J,
                  (Zeta23.CCM.quadraticForm
                    (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨L₀, hL₀, hnegAll⟩ :=
    eventually_all_apertures_have_negativeCanonicalSourceWitness_of_offLine_zero
      ρ₀ hoff
  refine ⟨L₀, hL₀, ?_⟩
  intro Q hQ L₁ hcell hL₁
  obtain ⟨N, hN, u, hflat, hneg⟩ := hnegAll L₁ hL₁
  obtain ⟨J, hJopen, hL₁J, hJcell, hpersist⟩ :=
    Zeta23.CCM.exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
      Q N hQ u hcell hneg
  exact ⟨N, hN, u, hflat, J, hJopen, hL₁J, hJcell, hpersist⟩

/-- Existential off-line-zero wrapper for fixed-cell witness persistence. -/
theorem
    eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ Q : ℕ, 1 ≤ Q →
        ∀ L₁ : ℝ,
          L₁ ∈ Zeta23.CCM.fixedCanonicalCutoffCell Q →
          L₀ < L₁ →
          ∃ N : ℕ, 1 ≤ N ∧
            ∃ u : Fin (2 * N + 1) → ℂ,
              Zeta23.CCM.BoundaryFlatCoefficients N u ∧
              ∃ J : Set ℝ,
                IsOpen J ∧
                L₁ ∈ J ∧
                J ⊆ Zeta23.CCM.fixedCanonicalCutoffCell Q ∧
                ∀ L ∈ J,
                  (Zeta23.CCM.quadraticForm
                    (Zeta23.CCM.canonicalSourceMatrix L N) u).re < 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
      ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_exists_offLine_zero
