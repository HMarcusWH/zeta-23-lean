import Zeta23.CCM.ZeroShiftSchurEndpoint
import Zeta23.ExceptionalZero.GlobalFirstBadZeroShiftSchurDichotomy

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A2-ENDPOINT exceptional-zero endpoint

This module composes the #124 zero-shift kernel/range dichotomy with the exact
zero-shift complete-square theorem. A hypothetical off-critical-line zero now
forces one common global-first-bad state in one of two mechanisms:

* decoupled: the canonical cubic coupling admits a zero-shift preimage and the
  canonical zero-shift Schur endpoint is strictly negative;
* resonant: a kernel vector couples nontrivially to the cubic channel and the
  exact #124 negative-shift resonant identity/lower bound holds at the same
  negative secular root.

The regular branch is strengthened from zero-shift solvability to a strict
negative zero-shift obstruction. The resonant branch is not weakened or
excluded. No inverse of `A` at zero is introduced, and RH remains open.
-/

/-- A hypothetical off-line zero forces one global-first-bad state in either a
strictly negative canonical zero-shift Schur endpoint branch or the existing
quantitatively resonant kernel branch. -/
theorem exists_globalFirstBad_zeroShiftSchurEndpointDichotomy_of_offLine_zero
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
              (
                (
                  ∃ x₀ : intrinsicParityPredecessorSubspace p Nprev,
                    intrinsicPredecessorBlock p L Nprev x₀ =
                      intrinsicShellToPredecessor p L Nprev
                        (intrinsicCubicShellPart p Nprev) ∧
                    Complex.re
                        (cubicZeroShiftSchurEndpoint p L Nprev x₀) < 0 ∧
                    ∀ x : intrinsicParityPredecessorSubspace p Nprev,
                      intrinsicPredecessorBlock p L Nprev x =
                          intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev) →
                        cubicZeroShiftSchurEndpoint p L Nprev x =
                          cubicZeroShiftSchurEndpoint p L Nprev x₀
                )
                ∨
                ∃ z : intrinsicParityPredecessorSubspace p Nprev,
                  intrinsicPredecessorBlock p L Nprev z = 0 ∧
                  inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ≠ 0 ∧
                  inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) =
                    (-lam : ℂ) *
                      inner ℂ
                        (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                        ((shiftedIntrinsicPredecessorResolvent
                            p hL Nprev (hprevBoth p) lam hlam
                            (intrinsicShellToPredecessor p L Nprev
                              (intrinsicCubicShellPart p Nprev)) :
                            intrinsicParityPredecessorSubspace p Nprev) :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ∧
                  ‖inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1))‖ ^ 2 ≤
                    (-lam) * ‖z‖ ^ 2 *
                      Complex.re
                        (inner ℂ
                          ((shiftedIntrinsicPredecessorResolvent
                              p hL Nprev (hprevBoth p) lam hlam
                              (intrinsicShellToPredecessor p L Nprev
                                (intrinsicCubicShellPart p Nprev)) :
                              intrinsicParityPredecessorSubspace p Nprev) :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                          ((intrinsicShellToPredecessor p L Nprev
                              (intrinsicCubicShellPart p Nprev) :
                              intrinsicParityPredecessorSubspace p Nprev) :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
              ) := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, hroot, hbranch⟩ :=
    exists_globalFirstBad_zeroShiftSchurDichotomy_of_offLine_zero ρ₀ hoff
  rcases hbranch with hdec | hres
  · obtain ⟨x₀, hx₀, _hinnerUnique⟩ := hdec
    have hneg :=
      cubicZeroShiftSchurEndpoint_re_neg_of_explicit_root
        p hL Nprev hNprev (hprevBoth p) x₀ hx₀ lam hlam hroot
    refine ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot, Or.inl ⟨x₀, hx₀, hneg, ?_⟩⟩
    intro x hx
    exact cubicZeroShiftSchurEndpoint_eq_of_preimages
      p L Nprev x x₀ hx hx₀
  · exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot, Or.inr hres⟩

/-- Existential off-line-zero wrapper for the strict zero-shift endpoint versus
resonance dichotomy. -/
theorem exists_globalFirstBad_zeroShiftSchurEndpointDichotomy_of_exists_offLine_zero
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
              (
                (
                  ∃ x₀ : intrinsicParityPredecessorSubspace p Nprev,
                    intrinsicPredecessorBlock p L Nprev x₀ =
                      intrinsicShellToPredecessor p L Nprev
                        (intrinsicCubicShellPart p Nprev) ∧
                    Complex.re
                        (cubicZeroShiftSchurEndpoint p L Nprev x₀) < 0 ∧
                    ∀ x : intrinsicParityPredecessorSubspace p Nprev,
                      intrinsicPredecessorBlock p L Nprev x =
                          intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev) →
                        cubicZeroShiftSchurEndpoint p L Nprev x =
                          cubicZeroShiftSchurEndpoint p L Nprev x₀
                )
                ∨
                ∃ z : intrinsicParityPredecessorSubspace p Nprev,
                  intrinsicPredecessorBlock p L Nprev z = 0 ∧
                  inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ≠ 0 ∧
                  inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1)) =
                    (-lam : ℂ) *
                      inner ℂ
                        (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                        ((shiftedIntrinsicPredecessorResolvent
                            p hL Nprev (hprevBoth p) lam hlam
                            (intrinsicShellToPredecessor p L Nprev
                              (intrinsicCubicShellPart p Nprev)) :
                            intrinsicParityPredecessorSubspace p Nprev) :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ∧
                  ‖inner ℂ
                      (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                      ((intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev) :
                          intrinsicParityPredecessorSubspace p Nprev) :
                        euclideanParityBoundaryFlatSubspace p (Nprev + 1))‖ ^ 2 ≤
                    (-lam) * ‖z‖ ^ 2 *
                      Complex.re
                        (inner ℂ
                          ((shiftedIntrinsicPredecessorResolvent
                              p hL Nprev (hprevBoth p) lam hlam
                              (intrinsicShellToPredecessor p L Nprev
                                (intrinsicCubicShellPart p Nprev)) :
                              intrinsicParityPredecessorSubspace p Nprev) :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                          ((intrinsicShellToPredecessor p L Nprev
                              (intrinsicCubicShellPart p Nprev) :
                              intrinsicParityPredecessorSubspace p Nprev) :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1)))
              ) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_globalFirstBad_zeroShiftSchurEndpointDichotomy_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftSchurEndpointDichotomy_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftSchurEndpointDichotomy_of_exists_offLine_zero
