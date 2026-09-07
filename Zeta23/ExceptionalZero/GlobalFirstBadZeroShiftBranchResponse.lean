import Zeta23.CCM.ZeroShiftBranchResponse
import Zeta23.ExceptionalZero.GlobalFirstBadZeroShiftShellResponse

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A3b exceptional-zero endpoint

This module keeps the exact global-first-bad state from E4-A3a and sharpens
both zero-shift branches.

Regular branch:
* the canonical cubic kernel component vanishes;
* the E4-A3a shell response remains exact;
* its canonical scalar has strictly negative real part at the same forced
  negative explicit root.

Resonant branch:
* the canonical cubic kernel component is nonzero;
* its shifted-resolvent kernel coordinate satisfies the exact denominator-free
  pole identity and its divided corollary;
* the earlier arbitrary kernel witness, exact inner-product identity, and
  denominator-free quantitative bound are retained on the same state.

This is still classification/rigidity infrastructure.  Neither branch is
excluded.

Firewalls:
* `ker A` remains the projected successor predecessor-block kernel;
* no zero-shift inverse, spectral decomposition, or resolvent limit is used;
* no shell invariance or zero-shift eigenvector statement is claimed;
* no negative-root exclusion, positivity closure, finite-to-infinite closure,
  or RH theorem is claimed.
-/

/-- A hypothetical off-line zero forces one global-first-bad state with a
canonical regular-vs-resonant branch certificate. -/
theorem exists_globalFirstBad_zeroShiftBranchResponseDichotomy_of_offLine_zero
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
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ∧
                    cubicCouplingKernelPart p L Nprev = 0 ∧
                    Complex.re
                      (cubicZeroShiftShellResponseScalar p L Nprev x₀) < 0
                )
                ∨
                (
                  cubicCouplingKernelPart p L Nprev ≠ 0 ∧
                  (-lam : ℂ) •
                      intrinsicPredecessorKernelPart p L Nprev
                        (shiftedIntrinsicPredecessorResolvent
                          p hL Nprev (hprevBoth p) lam hlam
                          (intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev))) =
                    cubicCouplingKernelPart p L Nprev ∧
                  intrinsicPredecessorKernelPart p L Nprev
                      (shiftedIntrinsicPredecessorResolvent
                        p hL Nprev (hprevBoth p) lam hlam
                        (intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev))) =
                    ((-lam : ℂ)⁻¹) • cubicCouplingKernelPart p L Nprev ∧
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
                )
              ) := by
  obtain ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
    hglobal, hmin, hroot, hbranch⟩ :=
    exists_globalFirstBad_zeroShiftShellResponseDichotomy_of_offLine_zero ρ₀ hoff
  rcases hbranch with hdec | hres
  · obtain ⟨x₀, hx₀, hneg, hunique, hresponse, hendpointResponse⟩ := hdec
    have hkzero := cubicCouplingKernelPart_eq_zero_of_preimage
      p L Nprev x₀ hx₀
    have hsigmaNeg := cubicZeroShiftShellResponseScalar_re_neg_of_explicit_root
      p hL Nprev hNprev (hprevBoth p) x₀ hx₀ lam hlam hroot
    exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot,
      Or.inl ⟨x₀, hx₀, hneg, hunique, hresponse, hendpointResponse,
        hkzero, hsigmaNeg⟩⟩
  · obtain ⟨z, hz, hzbne, hid, hbound⟩ := hres
    have hkne : cubicCouplingKernelPart p L Nprev ≠ 0 :=
      (cubicCouplingKernelPart_ne_zero_iff_resonant p L Nprev).2
        ⟨z, hz, hzbne⟩
    have hpole := neg_lam_smul_cubicCouplingKernelPart_resolvent_eq
      p hL Nprev (hprevBoth p) hlam
    have hpoleInv := cubicCouplingKernelPart_resolvent_eq_inv_neg_smul
      p hL Nprev (hprevBoth p) hlam
    exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot,
      Or.inr ⟨hkne, hpole, hpoleInv, z, hz, hzbne, hid, hbound⟩⟩

/-- Existential off-line-zero wrapper for the canonical branch-response
dichotomy. -/
theorem exists_globalFirstBad_zeroShiftBranchResponseDichotomy_of_exists_offLine_zero
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
                            euclideanParityBoundaryFlatSubspace p (Nprev + 1)) ∧
                    cubicCouplingKernelPart p L Nprev = 0 ∧
                    Complex.re
                      (cubicZeroShiftShellResponseScalar p L Nprev x₀) < 0
                )
                ∨
                (
                  cubicCouplingKernelPart p L Nprev ≠ 0 ∧
                  (-lam : ℂ) •
                      intrinsicPredecessorKernelPart p L Nprev
                        (shiftedIntrinsicPredecessorResolvent
                          p hL Nprev (hprevBoth p) lam hlam
                          (intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev))) =
                    cubicCouplingKernelPart p L Nprev ∧
                  intrinsicPredecessorKernelPart p L Nprev
                      (shiftedIntrinsicPredecessorResolvent
                        p hL Nprev (hprevBoth p) lam hlam
                        (intrinsicShellToPredecessor p L Nprev
                          (intrinsicCubicShellPart p Nprev))) =
                    ((-lam : ℂ)⁻¹) • cubicCouplingKernelPart p L Nprev ∧
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
                )
              ) := by
  obtain ⟨ρ₀, hρ₀⟩ := hoff
  exact
    exists_globalFirstBad_zeroShiftBranchResponseDichotomy_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftBranchResponseDichotomy_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftBranchResponseDichotomy_of_exists_offLine_zero
