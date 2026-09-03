import Zeta23.CCM.ParityBadness
import Zeta23.ExceptionalZero.ConstrainedFiniteObstruction

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# Fixed-parity first-bad obstruction

This module composes the finite canonical negative obstruction with exact
reversal parity.  A hypothetical off-critical-line zero now forces one fixed
positive aperture and one fixed parity sector that is bad from some finite size
onward.  Taking the least bad size in that parity exposes the exact
one-dimensional successor parity shell.

No constrained compression, eigenvalue theorem, KKT equation, positivity
theorem, finite-to-infinite theorem, or RH theorem is claimed here.
-/

/-- A hypothetical off-line zero forces one fixed parity-bad tail at one fixed
positive aperture. -/
theorem exists_fixedAperture_parityBad_tail_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ p : ReversalParity,
        ∃ N0 : ℕ, 2 ≤ N0 ∧
          ParityBad p L N0 ∧
          ∀ M : ℕ, N0 ≤ M → ParityBad p L M := by
  obtain ⟨L, hL, N, hN, u, hne, hmem, hneg⟩ :=
    exists_ne_zero_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
      ρ₀ hoff
  have hN2 :=
    two_le_of_ne_zero_mem_boundaryFlatSubspace hN hmem hne
  rcases parityBad_even_or_odd_of_negative hmem hneg with hbad | hbad
  · refine ⟨L, hL, .even, N, hN2, hbad, ?_⟩
    intro M hNM
    exact parityBad_persists_of_le .even hL hNM hbad
  · refine ⟨L, hL, .odd, N, hN2, hbad, ?_⟩
    intro M hNM
    exact parityBad_persists_of_le .odd hL hNM hbad

/-- Existential off-line-zero wrapper for the fixed-parity bad tail. -/
theorem exists_fixedAperture_parityBad_tail_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ p : ReversalParity,
        ∃ N0 : ℕ, 2 ≤ N0 ∧
          ParityBad p L N0 ∧
          ∀ M : ℕ, N0 ≤ M → ParityBad p L M := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_fixedAperture_parityBad_tail_of_offLine_zero ρ₀ hρ₀

/-- A hypothetical off-line zero forces a least bad size in one fixed parity.
That least size has a genuine predecessor Nprev>=1, its predecessor parity
sector is nonnegative by minimality, and the exact successor parity shell is
one complex dimension. -/
theorem exists_leastParityBad_oneDimShell_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ p : ReversalParity,
        ∃ Nprev Nstar : ℕ,
          1 ≤ Nprev ∧
          Nstar = Nprev + 1 ∧
          ParityBad p L Nstar ∧
          (∀ N : ℕ, N < Nstar → ¬ ParityBad p L N) ∧
          (∀ u : Fin (2 * Nprev + 1) → ℂ,
            u ∈ parityBoundaryFlatSubspace p Nprev →
              0 ≤ (quadraticForm (canonicalSourceMatrix L Nprev) u).re) ∧
          (∀ M : ℕ, Nstar ≤ M → ParityBad p L M) ∧
          Module.finrank ℂ (euclideanParitySuccShell p Nprev) = 1 := by
  obtain ⟨L, hL, p, N0, hN0, hbad0, htail0⟩ :=
    exists_fixedAperture_parityBad_tail_of_offLine_zero ρ₀ hoff
  obtain ⟨Nstar, hNstar2, hbadstar, hmin⟩ :=
    exists_least_parityBad_two_le p L ⟨N0, hbad0⟩
  let Nprev := Nstar - 1
  have hNprev : 1 ≤ Nprev := by
    dsimp [Nprev]
    omega
  have hsucc : Nstar = Nprev + 1 := by
    dsimp [Nprev]
    omega
  have hprevlt : Nprev < Nstar := by
    rw [hsucc]
    omega
  have hprevNonneg :
      ∀ u : Fin (2 * Nprev + 1) → ℂ,
        u ∈ parityBoundaryFlatSubspace p Nprev →
          0 ≤ (quadraticForm (canonicalSourceMatrix L Nprev) u).re := by
    intro u humem
    exact nonnegative_of_lt_least_parityBad
      p L hmin hprevlt u humem
  have htailstar :
      ∀ M : ℕ, Nstar ≤ M → ParityBad p L M := by
    intro M hNM
    exact parityBad_persists_of_le p hL hNM hbadstar
  have hshell :
      Module.finrank ℂ (euclideanParitySuccShell p Nprev) = 1 :=
    finrank_euclideanParitySuccShell p Nprev hNprev
  exact ⟨L, hL, p, Nprev, Nstar, hNprev, hsucc, hbadstar,
    hmin, hprevNonneg, htailstar, hshell⟩

/-- Existential off-line-zero wrapper for the least-bad one-dimensional-shell
endpoint. -/
theorem exists_leastParityBad_oneDimShell_of_exists_offLine_zero
    (hoff :
      ∃ ρ : zetaZeroConfig.carrier,
        (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∃ p : ReversalParity,
        ∃ Nprev Nstar : ℕ,
          1 ≤ Nprev ∧
          Nstar = Nprev + 1 ∧
          ParityBad p L Nstar ∧
          (∀ N : ℕ, N < Nstar → ¬ ParityBad p L N) ∧
          (∀ u : Fin (2 * Nprev + 1) → ℂ,
            u ∈ parityBoundaryFlatSubspace p Nprev →
              0 ≤ (quadraticForm (canonicalSourceMatrix L Nprev) u).re) ∧
          (∀ M : ℕ, Nstar ≤ M → ParityBad p L M) ∧
          Module.finrank ℂ (euclideanParitySuccShell p Nprev) = 1 := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_leastParityBad_oneDimShell_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_fixedAperture_parityBad_tail_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_fixedAperture_parityBad_tail_of_exists_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_leastParityBad_oneDimShell_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_leastParityBad_oneDimShell_of_exists_offLine_zero
