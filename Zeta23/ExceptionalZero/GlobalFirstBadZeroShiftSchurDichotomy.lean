import Zeta23.CCM.ZeroShiftSchurDichotomy
import Zeta23.ExceptionalZero.GlobalFirstBadCubicMetricResonance

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# FIRST-BAD-RIGIDITY-E4-A2 exceptional-zero endpoint

This module composes the E4-A2 kernel/range infrastructure with the existing
post-#122 global-first-bad endpoint. A hypothetical off-critical-line zero
therefore forces one common finite state in one of two exact zero-shift
mechanisms:

* decoupled: the canonical cubic coupling annihilates `ker A`, so the
  zero-shift equation `A x₀ = b` has a solution and the quadratic value
  `⟪x₀,b⟫` is independent of the selected solution;
* resonant: a kernel vector couples nontrivially to the cubic channel and the
  exact negative-shift resolvent identity/lower bound holds at the same
  negative secular root.

No inverse of `A` at zero is introduced. This is a classification, not a
contradiction. No branch is excluded and RH remains open.
-/

/-- A hypothetical off-line zero forces one global-first-bad state in either
the decoupled zero-shift-solve branch or the quantitatively resonant kernel
branch. -/
theorem exists_globalFirstBad_zeroShiftSchurDichotomy_of_offLine_zero
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
                    ∀ x : intrinsicParityPredecessorSubspace p Nprev,
                      intrinsicPredecessorBlock p L Nprev x =
                          intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev) →
                        inner ℂ
                            (x : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                            ((intrinsicShellToPredecessor p L Nprev
                                (intrinsicCubicShellPart p Nprev) :
                                intrinsicParityPredecessorSubspace p Nprev) :
                              euclideanParityBoundaryFlatSubspace p (Nprev + 1)) =
                          inner ℂ
                            (x₀ : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                            ((intrinsicShellToPredecessor p L Nprev
                                (intrinsicCubicShellPart p Nprev) :
                                intrinsicParityPredecessorSubspace p Nprev) :
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
    hglobal, hmin, hroot, _hbridge, _hnonneg, _hbound, _hres⟩ :=
    exists_globalFirstBad_cubicMetricResonance_of_offLine_zero ρ₀ hoff
  let b := intrinsicShellToPredecessor p L Nprev
    (intrinsicCubicShellPart p Nprev)
  by_cases hzero :
      ∀ z : intrinsicParityPredecessorSubspace p Nprev,
        intrinsicPredecessorBlock p L Nprev z = 0 →
          inner ℂ
            (z : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
            (b : euclideanParityBoundaryFlatSubspace p (Nprev + 1)) = 0
  · have hsolve :=
      exists_cubicCoupling_zeroShift_preimage_and_inner_unique
        p L Nprev (by simpa [b] using hzero)
    exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot, Or.inl (by simpa [b] using hsolve)⟩
  · push_neg at hzero
    obtain ⟨z, hz, hzb⟩ := hzero
    have hid :=
      inner_intrinsicPredecessorBlock_kernel_resolvent_eq
        p hL Nprev (hprevBoth p) hlam z b hz
    have hlow :=
      norm_sq_inner_kernel_coupling_le_neg_mul_norm_sq_re_inner_resolvent
        p hL Nprev (hprevBoth p) hlam z b hz
    exact ⟨L, hL, Nprev, hNprev, p, lam, hlam, hprevBoth,
      hglobal, hmin, hroot, Or.inr ⟨z, hz, by simpa [b] using hzb,
        by simpa [b] using hid, by simpa [b] using hlow⟩⟩

/-- Existential off-line-zero wrapper for the E4-A2 dichotomy endpoint. -/
theorem exists_globalFirstBad_zeroShiftSchurDichotomy_of_exists_offLine_zero
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
                    ∀ x : intrinsicParityPredecessorSubspace p Nprev,
                      intrinsicPredecessorBlock p L Nprev x =
                          intrinsicShellToPredecessor p L Nprev
                            (intrinsicCubicShellPart p Nprev) →
                        inner ℂ
                            (x : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                            ((intrinsicShellToPredecessor p L Nprev
                                (intrinsicCubicShellPart p Nprev) :
                                intrinsicParityPredecessorSubspace p Nprev) :
                              euclideanParityBoundaryFlatSubspace p (Nprev + 1)) =
                          inner ℂ
                            (x₀ : euclideanParityBoundaryFlatSubspace p (Nprev + 1))
                            ((intrinsicShellToPredecessor p L Nprev
                                (intrinsicCubicShellPart p Nprev) :
                                intrinsicParityPredecessorSubspace p Nprev) :
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
  exact exists_globalFirstBad_zeroShiftSchurDichotomy_of_offLine_zero ρ₀ hρ₀

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftSchurDichotomy_of_offLine_zero
#print axioms Zeta23.ExceptionalZero.exists_globalFirstBad_zeroShiftSchurDichotomy_of_exists_offLine_zero