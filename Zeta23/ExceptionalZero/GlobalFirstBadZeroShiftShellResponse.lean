import Zeta23.CCM.ZeroShiftShellResponse
import Zeta23.ExceptionalZero.GlobalFirstBadZeroShiftSchurEndpoint

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A3a exceptional-zero endpoint

This module strengthens only the regular branch of the exact #125 global
first-bad endpoint dichotomy.  At the same first-bad state and the same safe
negative secular root, a decoupled zero-shift preimage now carries the exact
canonical one-dimensional shell response

  sigma₀ • c = T u₀

and the exact endpoint identity

  S₀ = star(sigma₀) * <c,c>.

The resonant branch is carried through unchanged.  In particular, this is a
classification/refinement theorem, not a branch-exclusion theorem.

Firewalls:
* `T u₀` being pure shell does not make `u₀` an eigenvector;
* no shell invariance is claimed;
* no zero-shift inverse is introduced;
* the resonant branch is not weakened or excluded;
* no monotonicity, root uniqueness, negative-root exclusion, positivity,
  finite-to-infinite closure, or RH theorem is claimed.
-/

/-- A hypothetical off-line zero forces one global-first-bad state in either
an enhanced regular branch carrying the canonical shell response and endpoint
identity, or the unchanged quantitatively resonant kernel branch. -/
theorem exists_globalFirstBad_zeroShiftShellResponseDichotomy_of_offLine_zero
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
                    (∀ x : intrinsicParityPredecessorSubspace p Nprev,
                      intrinsicPredecessorBlock p L Nprev x =
                          intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev) →
                        cubicZeroShiftSchurEndpoint p L Nprev x =
                          cubicZeroShiftSchurEndpoint p L Nprev x₀) ∧
                    cubicZeroShiftShellResponseScalar p L Nprev x₀ •
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)) =
                      parityCompressedCanonical p L (Nprev + 1)
                        (cubicZeroShiftTrialVector p L Nprev x₀) ∧
                    cubicZeroShiftSchurEndpoint p L Nprev x₀ =
                      star (cubicZeroShiftShellResponseScalar p L Nprev x₀) *
                        inner ℂ
                          (intrinsicCubicShellPart p Nprev :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                          (intrinsicCubicShellPart p Nprev :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1))
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
    exists_globalFirstBad_zeroShiftSchurEndpointDichotomy_of_offLine_zero ρ₀ hoff
  rcases hbranch with hdec | hres
  · obtain ⟨x₀, hx₀, hneg, hunique⟩ := hdec
    have hresponse :=
      cubicZeroShiftShellResponseScalar_smul_cubic_eq
        p L Nprev hNprev x₀ hx₀
    have hendpointResponse :=
      cubicZeroShiftSchurEndpoint_eq_star_shellResponse_mul_inner
        p L Nprev hNprev x₀ hx₀
    exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot,
      Or.inl ⟨x₀, hx₀, hneg, hunique, hresponse, hendpointResponse⟩⟩
  · exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot, Or.inr hres⟩

/-- Existential off-line-zero wrapper for the enhanced regular shell-response
versus unchanged resonance dichotomy. -/
theorem exists_globalFirstBad_zeroShiftShellResponseDichotomy_of_exists_offLine_zero
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
                    (∀ x : intrinsicParityPredecessorSubspace p Nprev,
                      intrinsicPredecessorBlock p L Nprev x =
                          intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev) →
                        cubicZeroShiftSchurEndpoint p L Nprev x =
                          cubicZeroShiftSchurEndpoint p L Nprev x₀) ∧
                    cubicZeroShiftShellResponseScalar p L Nprev x₀ •
                        (intrinsicCubicShellPart p Nprev :
                          euclideanParityBoundaryFlatSubspace p (Nprev + 1)) =
                      parityCompressedCanonical p L (Nprev + 1)
                        (cubicZeroShiftTrialVector p L Nprev x₀) ∧
                    cubicZeroShiftSchurEndpoint p L Nprev x₀ =
                      star (cubicZeroShiftShellResponseScalar p L Nprev x₀) *
                        inner ℂ
                          (intrinsicCubicShellPart p Nprev :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                          (intrinsicCubicShellPart p Nprev :
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1))
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
    exists_globalFirstBad_zeroShiftShellResponseDichotomy_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftShellResponseDichotomy_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftShellResponseDichotomy_of_exists_offLine_zero
