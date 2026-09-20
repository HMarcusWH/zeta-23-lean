import Zeta23.CCM.CrossParityTrialReconstruction

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A3c: correction-functional Riesz representation

The safe odd predecessor-correction functional is a complex-linear functional
on the intrinsic predecessor space.  This module exposes the exact vector
representing that functional in the ambient Euclidean inner product:

  chi(y) = <R b, y> / <c,c>,

where c is the canonical odd cubic shell vector, b is its projected
predecessor forcing, and R is the negative-shift predecessor resolvent.

This is a representation theorem only.  The numerator is a mixed resolvent
pairing, so no reality, sign, phase, branch exclusion, negative-root exclusion,
or RH claim is made.
-/

/-- Exact Riesz-type representation of the safe odd correction functional. -/
theorem oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (y : intrinsicParityPredecessorSubspace .odd N) :
    oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam y =
      inner ℂ
          ((shiftedIntrinsicPredecessorResolvent .odd
              hL N hprevOdd lam hlam
              (intrinsicShellToPredecessor .odd L N
                (intrinsicCubicShellPart .odd N)) :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (y : euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  let c := intrinsicCubicShellPart .odd N
  let b := intrinsicShellToPredecessor .odd L N c
  let R := shiftedIntrinsicPredecessorResolvent .odd hL N hprevOdd lam hlam
  let chi := oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
  let cV : euclideanParityBoundaryFlatSubspace .odd (N + 1) := c
  let den := inner ℂ cV cV
  have hchiInner :
      chi y =
        inner ℂ cV
            (parityCompressedCanonical .odd L (N + 1)
              ((R y : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den := by
    change
      intrinsicCubicQuotientCoordinate .odd N
          (parityCompressedCanonical .odd L (N + 1)
            ((R y : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        inner ℂ cV
            (parityCompressedCanonical .odd L (N + 1)
              ((R y : intrinsicParityPredecessorSubspace .odd N) :
                euclideanParityBoundaryFlatSubspace .odd (N + 1))) /
          inner ℂ cV cV
    exact
      intrinsicCubicQuotientCoordinate_eq_inner_div
        .odd N hN
        (parityCompressedCanonical .odd L (N + 1)
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)))
  have hsymT :
      inner ℂ cV
          (parityCompressedCanonical .odd L (N + 1)
            ((R y : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
        inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    exact
      (parityCompressedCanonical_isSymmetric .odd L (N + 1)
        cV
        ((R y : intrinsicParityPredecessorSubspace .odd N) :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))).symm
  have hTcRy :
      inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    let Ty := parityCompressedCanonical .odd L (N + 1) cV
    have hrec := intrinsicPredecessorPart_add_shellPart .odd N Ty
    have hpredTy : intrinsicPredecessorPart .odd N Ty = b := by rfl
    have hort := inner_intrinsicShell_predecessor_eq_zero
      .odd N (intrinsicShellPart .odd N Ty) (R y)
    calc
      inner ℂ Ty
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          ((intrinsicPredecessorPart .odd N Ty :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) +
        inner ℂ
          ((intrinsicShellPart .odd N Ty : intrinsicParitySuccShell .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
          rw [← inner_add_left]
          exact congrArg
            (fun z : euclideanParityBoundaryFlatSubspace .odd (N + 1) =>
              inner ℂ z
                ((R y : intrinsicParityPredecessorSubspace .odd N) :
                  euclideanParityBoundaryFlatSubspace .odd (N + 1))) hrec.symm
      _ = inner ℂ
          ((intrinsicPredecessorPart .odd N Ty :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hort, add_zero]
      _ = inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
        rw [hpredTy]
  have hRby :
      inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (y : euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    simpa [R] using
      shiftedIntrinsicPredecessorResolvent_isSymmetric
        .odd hL N hprevOdd hlam b y
  calc
    chi y =
        inner ℂ cV
          (parityCompressedCanonical .odd L (N + 1)
            ((R y : intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) / den :=
      hchiInner
    _ = inner ℂ
          (parityCompressedCanonical .odd L (N + 1) cV)
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
      rw [hsymT]
    _ = inner ℂ
          (b : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((R y : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
      rw [hTcRy]
    _ = inner ℂ
          ((R b : intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (y : euclideanParityBoundaryFlatSubspace .odd (N + 1)) / den := by
      rw [← hRby]

/-- The remaining alpha freedom is exactly one mixed resolvent pairing. -/
theorem one_sub_crossParitySecularAlpha_eq_resolvent_pairing_div
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    1 - crossParitySecularAlpha hL N hprevOdd lam hlam =
      inner ℂ
          ((shiftedIntrinsicPredecessorResolvent .odd
              hL N hprevOdd lam hlam
              (intrinsicShellToPredecessor .odd L N
                (intrinsicCubicShellPart .odd N)) :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (oddIndexCubicShellPredecessorPart N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  change
    1 -
        (1 -
          oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
            (oddIndexCubicShellPredecessorPart N)) = _
  calc
    1 -
        (1 -
          oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
            (oddIndexCubicShellPredecessorPart N)) =
      oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
        (oddIndexCubicShellPredecessorPart N) := by ring
    _ = _ :=
      oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div
        hL N hN hprevOdd lam hlam (oddIndexCubicShellPredecessorPart N)

/-- The Gamma correction has the same Riesz representative, evaluated on the
odd cubic-generator predecessor direction. -/
theorem one_sub_crossParitySecularGamma_eq_resolvent_pairing_div
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    1 - crossParitySecularGamma hL N hprevOdd lam hlam =
      inner ℂ
          ((shiftedIntrinsicPredecessorResolvent .odd
              hL N hprevOdd lam hlam
              (intrinsicShellToPredecessor .odd L N
                (intrinsicCubicShellPart .odd N)) :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (oddCubicGeneratorPredecessorPart N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) /
        inner ℂ
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (intrinsicCubicShellPart .odd N :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
  change
    1 -
        (1 -
          oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
            (oddCubicGeneratorPredecessorPart N)) = _
  calc
    1 -
        (1 -
          oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
            (oddCubicGeneratorPredecessorPart N)) =
      oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam
        (oddCubicGeneratorPredecessorPart N) := by ring
    _ = _ :=
      oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div
        hL N hN hprevOdd lam hlam (oddCubicGeneratorPredecessorPart N)

end Zeta23.CCM

#print axioms Zeta23.CCM.oddSafeSecularCorrectionFunctional_eq_resolvent_pairing_div
#print axioms Zeta23.CCM.one_sub_crossParitySecularAlpha_eq_resolvent_pairing_div
#print axioms Zeta23.CCM.one_sub_crossParitySecularGamma_eq_resolvent_pairing_div
