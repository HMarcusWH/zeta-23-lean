import Zeta23.CCM.CubicSecularEquation
import Zeta23.ExceptionalZero.GlobalFirstBadCubicNormalizedSchur

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E3-A exceptional-zero endpoint

The merged E2 endpoint supplies a hypothetical off-critical-line zero with one
global first-bad finite state, a negative parity-compressed eigenmode, and
nonnegative predecessor sectors. E3-A turns that same state into an exact
canonical scalar root problem: the shifted-resolvent trial vector is nonzero,
is itself an eigenmode, and its cubic secular scalar vanishes. The scalar root
is also theorem-identified with existence of a nonzero eigenmode at that exact
negative shift.

This remains a finite-dimensional reduction. No sign or monotonicity theorem
for the secular scalar is asserted, and RH remains open.
-/

/-- A hypothetical off-line zero forces a global first-bad finite state whose
canonical E3-A cubic secular scalar has an exact negative root. The predecessor
nonnegativity proof is retained for both parities, and the root is accompanied
by the exact root/eigenmode equivalence. -/
theorem exists_globalFirstBad_cubicSecularRoot_of_offLine_zero
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
              cubicSecularScalar p hL Nprev (hprevBoth p) lam hlam = 0 ∧
              (cubicSecularScalar p hL Nprev (hprevBoth p) lam hlam = 0 ↔
                ∃ u : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
                  u ≠ 0 ∧
                    parityCompressedCanonical p L (Nprev + 1) u =
                      (lam : ℂ) • u) := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, v, hvne, hveig,
    hglobal, hmin, hprevBoth, _hshellDim, _hkkt, _hcubicNe, _hcubicFactor,
    _hshellNe, _hcubicShellNe, _hbij, _R, _hRleft, _hresR, _hschurR,
    _hcubicSchurR⟩ :=
    exists_globalFirstBad_cubicNormalizedSchur_of_offLine_zero ρ₀ hoff
  have hiff :=
    cubicSecularScalar_eq_zero_iff_exists_eigenmode
      p hL Nprev hNprev (hprevBoth p) lam hlam
  have hroot :
      cubicSecularScalar p hL Nprev (hprevBoth p) lam hlam = 0 :=
    hiff.mpr ⟨v, hvne, hveig⟩
  have htrialNe :=
    cubicSecularTrialVector_ne_zero
      p hL Nprev hNprev (hprevBoth p) lam hlam
  have htrialEig :=
    (cubicSecularScalar_eq_zero_iff_trial_eigenmode
      p hL Nprev hNprev (hprevBoth p) lam hlam).mp hroot
  exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, htrialNe, htrialEig, hroot, hiff⟩

/-- Existential off-line-zero wrapper for the exact E3-A secular-root
endpoint. -/
theorem exists_globalFirstBad_cubicSecularRoot_of_exists_offLine_zero
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
              cubicSecularScalar p hL Nprev (hprevBoth p) lam hlam = 0 ∧
              (cubicSecularScalar p hL Nprev (hprevBoth p) lam hlam = 0 ↔
                ∃ u : euclideanParityBoundaryFlatSubspace p (Nprev + 1),
                  u ≠ 0 ∧
                    parityCompressedCanonical p L (Nprev + 1) u =
                      (lam : ℂ) • u) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_globalFirstBad_cubicSecularRoot_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicSecularRoot_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicSecularRoot_of_exists_offLine_zero
