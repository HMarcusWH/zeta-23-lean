import Zeta23.CCM.CubicExplicitSecular
import Zeta23.ExceptionalZero.GlobalFirstBadCubicSecularEquation

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E3-B2 exceptional-zero endpoint

PR #119 packages a hypothetical off-critical-line zero into one global
first-bad finite state carrying an exact negative root of the canonical quotient
secular scalar. E3-B2 identifies that scalar with the #113-oriented explicit
Schur scalar up to conjugation and a nonzero normalization, so the same global
state carries an exact negative root of the explicit Schur equation.

This remains a finite-dimensional reduction. No realness, sign, monotonicity,
root-count, root-exclusion, positivity, finite-to-infinite closure, or RH theorem
is claimed.
-/

/-- A hypothetical off-line zero forces a global first-bad finite state whose
explicit #113-oriented cubic Schur scalar has an exact negative root. -/
theorem exists_globalFirstBad_cubicExplicitSchurRoot_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ lam : ℝ, ∃ hlam : lam < 0,
            ∃ hprevBoth :
              ∀ q : ReversalParity,
                ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                  x ∈ euclideanParityBoundaryFlatSubspace q Nprev →
                    0 ≤ Complex.re
                      (inner ℂ
                        ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
              AnyParityBad L (Nprev + 1) ∧
              (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
              cubicSecularTrialVector p hL Nprev (hprevBoth p) lam hlam ≠ 0 ∧
              parityCompressedCanonical p L (Nprev + 1)
                  (cubicSecularTrialVector p hL Nprev (hprevBoth p) lam hlam) =
                (lam : ℂ) •
                  cubicSecularTrialVector p hL Nprev (hprevBoth p) lam hlam ∧
              cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam = 0 ∧
              (cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam = 0 ↔
                ∃ u : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
                  u ≠ 0 ∧
                    parityCompressedCanonical p L (Nprev + 1) u =
                      (lam : ℂ) • u) := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, htrialNe, htrialEig, hroot, _hiff⟩ :=
    exists_globalFirstBad_cubicSecularRoot_of_offLine_zero ρ₀ hoff
  have hbridge :=
    cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
      p hL Nprev hNprev (hprevBoth p) lam hlam
  have hrootExplicit :
      cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam = 0 :=
    hbridge.mpr hroot
  have hiffExplicit :=
    cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode
      p hL Nprev hNprev (hprevBoth p) lam hlam
  exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, htrialNe, htrialEig, hrootExplicit, hiffExplicit⟩

/-- Existential off-line-zero wrapper for the explicit E3-B2 Schur-root
endpoint. -/
theorem exists_globalFirstBad_cubicExplicitSchurRoot_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ lam : ℝ, ∃ hlam : lam < 0,
            ∃ hprevBoth :
              ∀ q : ReversalParity,
                ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
                  x ∈ euclideanParityBoundaryFlatSubspace q Nprev →
                    0 ≤ Complex.re
                      (inner ℂ
                        ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
              AnyParityBad L (Nprev + 1) ∧
              (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
              cubicSecularTrialVector p hL Nprev (hprevBoth p) lam hlam ≠ 0 ∧
              parityCompressedCanonical p L (Nprev + 1)
                  (cubicSecularTrialVector p hL Nprev (hprevBoth p) lam hlam) =
                (lam : ℂ) •
                  cubicSecularTrialVector p hL Nprev (hprevBoth p) lam hlam ∧
              cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam = 0 ∧
              (cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam = 0 ↔
                ∃ u : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
                  u ≠ 0 ∧
                    parityCompressedCanonical p L (Nprev + 1) u =
                      (lam : ℂ) • u) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_globalFirstBad_cubicExplicitSchurRoot_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicExplicitSchurRoot_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicExplicitSchurRoot_of_exists_offLine_zero
