import Zeta23.CCM.ZeroResonanceCoupling
import Zeta23.ExceptionalZero.GlobalFirstBadCubicExplicitSecular

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E3-B1 / E4-A1 exceptional-zero endpoint

This module composes the metric and zero-resonance theorem layers with the
already-proved E3-B2 global-first-bad explicit secular root. A hypothetical
off-critical-line zero therefore produces one common finite state carrying:

* an exact negative root of the explicit cubic Schur scalar;
* the real, unconjugated identification with the exact quotient secular scalar;
* the `mu = 0` root metric/deformation constraints;
* the exact classification of cubic coupling on `ker A`, where
  `A = P_W T|_W` is the projected successor predecessor block.

No assertion is made that the cubic coupling vanishes on `ker A`. `ker A` is
not identified here with the predecessor-size compressed-operator kernel. No
monotonicity, root-count, root-exclusion, positivity closure, or RH theorem is
claimed.
-/

/-- A hypothetical off-line zero forces one global first-bad finite state
carrying the real explicit secular root, its first metric bound, and the exact
zero-resonance coupling classification. -/
theorem exists_globalFirstBad_cubicMetricResonance_of_offLine_zero
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
              cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam = 0 ∧
              cubicSecularScalar p hL Nprev (hprevBoth p) lam hlam =
                cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam /
                  inner ℂ
                    (intrinsicCubicShellPart p Nprev :
                      euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                    (intrinsicCubicShellPart p Nprev :
                      euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ∧
              0 ≤
                Complex.re
                  (inner ℂ
                      (parityCompressedCanonical p L (Nprev + 1)
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                      (intrinsicCubicShellPart p Nprev :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                    (lam : ℂ) *
                      inner ℂ
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))) ∧
              (-lam) *
                Complex.re
                  (inner ℂ
                      (parityCompressedCanonical p L (Nprev + 1)
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                      (intrinsicCubicShellPart p Nprev :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                    (lam : ℂ) *
                      inner ℂ
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))) ≤
                ‖intrinsicShellToPredecessor p L Nprev
                    (intrinsicCubicShellPart p Nprev)‖ ^ 2 ∧
              (∀ z : intrinsicParityPredecessorSubspace p Nprev,
                intrinsicPredecessorBlock p L Nprev z = 0 →
                  (inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0 ↔
                    parityCompressedCanonical p L (Nprev + 1)
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0)) := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, _htrialNe, _htrialEig, hroot, _hiff⟩ :=
    exists_globalFirstBad_cubicExplicitSchurRoot_of_offLine_zero ρ₀ hoff
  have hbridge :=
    cubicSecularScalar_eq_cubicExplicitSchurScalar_div
      p hL Nprev hNprev (hprevBoth p) lam hlam
  have hnonneg :=
    cubicExplicitSchurRoot_shift_nonnegative
      p hL Nprev (hprevBoth p) lam hlam hroot
  have hbound :=
    cubicExplicitSchurRoot_metric_bound
      p hL Nprev (hprevBoth p) lam hlam hroot
  have hres :
      ∀ z : intrinsicParityPredecessorSubspace p Nprev,
        intrinsicPredecessorBlock p L Nprev z = 0 →
          (inner ℂ
              (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
              ((intrinsicShellToPredecessor p L Nprev
                  (intrinsicCubicShellPart p Nprev) :
                  intrinsicParityPredecessorSubspace p Nprev) :
                euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0 ↔
            parityCompressedCanonical p L (Nprev + 1)
              (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0) := by
    intro z hz
    exact
      inner_cubicCoupling_eq_zero_iff_successor_zero_of_intrinsicPredecessorBlock_eq_zero
        p L Nprev hNprev z hz
  exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, hroot, hbridge, hnonneg, hbound, hres⟩

/-- Existential off-line-zero wrapper for the metric/resonance endpoint. -/
theorem exists_globalFirstBad_cubicMetricResonance_of_exists_offLine_zero
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
              cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam = 0 ∧
              cubicSecularScalar p hL Nprev (hprevBoth p) lam hlam =
                cubicExplicitSchurScalar p hL Nprev (hprevBoth p) lam hlam /
                  inner ℂ
                    (intrinsicCubicShellPart p Nprev :
                      euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                    (intrinsicCubicShellPart p Nprev :
                      euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ∧
              0 ≤
                Complex.re
                  (inner ℂ
                      (parityCompressedCanonical p L (Nprev + 1)
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                      (intrinsicCubicShellPart p Nprev :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                    (lam : ℂ) *
                      inner ℂ
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))) ∧
              (-lam) *
                Complex.re
                  (inner ℂ
                      (parityCompressedCanonical p L (Nprev + 1)
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
                      (intrinsicCubicShellPart p Nprev :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) -
                    (lam : ℂ) *
                      inner ℂ
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1))) ≤
                ‖intrinsicShellToPredecessor p L Nprev
                    (intrinsicCubicShellPart p Nprev)‖ ^ 2 ∧
              (∀ z : intrinsicParityPredecessorSubspace p Nprev,
                intrinsicPredecessorBlock p L Nprev z = 0 →
                  (inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0 ↔
                    parityCompressedCanonical p L (Nprev + 1)
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0)) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact exists_globalFirstBad_cubicMetricResonance_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicMetricResonance_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_cubicMetricResonance_of_exists_offLine_zero
