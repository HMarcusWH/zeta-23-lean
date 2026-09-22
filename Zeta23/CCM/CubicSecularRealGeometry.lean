import Zeta23.CCM.CanonicalShiftedConjugationGeometry
import Zeta23.CCM.CubicSecularEquation

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Canonical cubic secular real geometry

The canonical safe negative-shift trial is defined over the reals before any
secular-root condition is imposed.  The shell is conjugation-fixed, its
predecessor forcing is conjugation-fixed, and the safe shifted resolvent
commutes with conjugation.

Thus the canonical trial itself is fixed by coordinate conjugation for every
safe real negative shift.

No secular-root hypothesis, eigenmode hypothesis, sign conclusion, branch
exclusion, negative-root exclusion, or RH claim is asserted.
-/

/-- The canonical E3-A trial is fixed by coordinate conjugation for every safe
real negative shift. -/
theorem cubicSecularTrialVector_conj_fixed
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    parityConj p (N + 1)
        (cubicSecularTrialVector p hL N hprev lam hlam) =
      cubicSecularTrialVector p hL N hprev lam hlam := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hb :
      intrinsicPredecessorConj p N b = b := by
    simpa [b, c] using intrinsicCubicShellForcing_conj_fixed p L N
  have hRconj :=
    shiftedIntrinsicPredecessorResolvent_conj
      p hL N hprev lam hlam b
  rw [hb] at hRconj
  have hRfix :
      intrinsicPredecessorConj p N (R b) = R b := by
    simpa [R] using hRconj.symm
  have hRambient :
      euclideanConj
          ((((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) =
        (((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
    have h :=
      congrArg
        (fun z : intrinsicParityPredecessorSubspace p N =>
          (((z : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) hRfix
    simpa [intrinsicPredecessorConj, parityConj] using h
  have hcfix := intrinsicCubicShellPart_conj_fixed p N
  have hcambient :
      euclideanConj
          ((((c : intrinsicParitySuccShell p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) =
        (((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
    have h :=
      congrArg
        (fun z : intrinsicParitySuccShell p N =>
          (((z : intrinsicParitySuccShell p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) hcfix
    simpa [intrinsicShellConj, parityConj, c] using h
  apply Subtype.ext
  change
    euclideanConj
        (- (((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) +
          (((c : intrinsicParitySuccShell p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) =
      - (((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) +
        (((c : intrinsicParitySuccShell p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
  rw [euclideanConj_add, euclideanConj_neg, hRambient, hcambient]

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicSecularTrialVector_conj_fixed
