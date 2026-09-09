import Zeta23.CCM.CanonicalOneStepDomination
import Zeta23.ExceptionalZero.GlobalFirstBadCubicExplicitSecular

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A4b2a global endpoint

The CCM module proves a conditional statement only: if the canonical one-step
domination certificate holds at a predecessor-nonnegative state, then the
explicit cubic Schur scalar has no negative root.

The existing global first-bad reduction says a hypothetical off-line zeta zero
produces exactly such a predecessor-nonnegative finite state together with an
exact negative explicit Schur root.  Therefore any off-line zero forces the
new finite domination certificate to fail.

This is a finite arithmetic reduction, not a proof that domination holds.
No RH theorem is claimed.
-/

/-- A hypothetical off-line zero forces a global first-bad finite state at
which canonical one-step domination fails. -/
theorem exists_globalFirstBad_not_canonicalOneStepDomination_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ hprev :
            ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
              x ∈ euclideanParityBoundaryFlatSubspace p Nprev →
                0 ≤ Complex.re
                  (inner ℂ
                    ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
            AnyParityBad L (Nprev + 1) ∧
            (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
            ¬ canonicalOneStepDomination p L Nprev := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, _htrialNe, _htrialEig, hroot, _hiff⟩ :=
    exists_globalFirstBad_cubicExplicitSchurRoot_of_offLine_zero ρ₀ hoff
  let hprev := hprevBoth p
  refine ⟨L, hL, Nprev, hNprev, p, hprev, hglobal, hmin, ?_⟩
  intro hdom
  have hne :=
    cubicExplicitSchurScalar_ne_zero_of_canonicalOneStepDomination
      p hL Nprev hNprev hprev hdom lam hlam
  exact hne hroot

/-- Existential off-line-zero wrapper for the domination-failure endpoint. -/
theorem exists_globalFirstBad_not_canonicalOneStepDomination_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ hprev :
            ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
              x ∈ euclideanParityBoundaryFlatSubspace p Nprev →
                0 ≤ Complex.re
                  (inner ℂ
                    ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
            AnyParityBad L (Nprev + 1) ∧
            (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
            ¬ canonicalOneStepDomination p L Nprev := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_globalFirstBad_not_canonicalOneStepDomination_of_offLine_zero
    ρ₀ hρ₀

/-- Strong finite countercertificate form: an off-line zero forces either a
negative cubic-shell energy or a predecessor vector with negative canonical
one-step determinant at a global first-bad state. -/
theorem exists_globalFirstBad_negative_shell_or_oneStepDeterminant_of_offLine_zero
    (ρ₀ : zetaZeroConfig.carrier)
    (hoff : (ρ₀ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ hprev :
            ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
              x ∈ euclideanParityBoundaryFlatSubspace p Nprev →
                0 ≤ Complex.re
                  (inner ℂ
                    ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
            AnyParityBad L (Nprev + 1) ∧
            (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
            (cubicShellRealEnergy p L Nprev < 0 ∨
              ∃ w : intrinsicParityPredecessorSubspace p Nprev,
                cubicOneStepDeterminant p L Nprev w < 0) := by
  obtain ⟨L, hL, Nprev, hNprev, p, hprev,
    hglobal, hmin, hfail⟩ :=
    exists_globalFirstBad_not_canonicalOneStepDomination_of_offLine_zero
      ρ₀ hoff
  have hexplicit :=
    (not_canonicalOneStepDomination_iff p L Nprev).mp hfail
  exact ⟨L, hL, Nprev, hNprev, p, hprev,
    hglobal, hmin, hexplicit⟩

/-- Existential off-line-zero wrapper for the explicit finite sign-failure
countercertificate. -/
theorem exists_globalFirstBad_negative_shell_or_oneStepDeterminant_of_exists_offLine_zero
    (hoff : ∃ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L : ℝ, ∃ hL : 0 < L,
      ∃ Nprev : ℕ, ∃ hNprev : 1 ≤ Nprev,
        ∃ p : ReversalParity,
          ∃ hprev :
            ∀ x : EuclideanSpace ℂ (Fin (2 * Nprev + 1)),
              x ∈ euclideanParityBoundaryFlatSubspace p Nprev →
                0 ≤ Complex.re
                  (inner ℂ
                    ((canonicalSourceMatrix L Nprev).toEuclideanLin x) x),
            AnyParityBad L (Nprev + 1) ∧
            (∀ N : ℕ, N < Nprev + 1 → ¬ AnyParityBad L N) ∧
            (cubicShellRealEnergy p L Nprev < 0 ∨
              ∃ w : intrinsicParityPredecessorSubspace p Nprev,
                cubicOneStepDeterminant p L Nprev w < 0) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_globalFirstBad_negative_shell_or_oneStepDeterminant_of_offLine_zero
      ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_not_canonicalOneStepDomination_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_negative_shell_or_oneStepDeterminant_of_offLine_zero
