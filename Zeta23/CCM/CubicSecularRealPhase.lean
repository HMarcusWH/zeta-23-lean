import Zeta23.CCM.CanonicalConjugationGeometry
import Zeta23.CCM.CubicSecularEquation

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Canonical cubic secular real phase

A safe negative secular root produces a canonically normalized eigenmode whose
cubic quotient coordinate is exactly one.  Because the compressed canonical
operator commutes with coordinate conjugation, the conjugate is another
eigenmode at the same real eigenvalue.  The quotient coordinate also conjugates
and therefore remains one.  Existing E3-A normalization uniqueness then forces
the conjugated state to equal the original canonical trial.

No eigenvalue-simplicity assumption and no reality theorem for the shifted
resolvent are used.
-/

/-- A canonical cubic secular trial at a genuine safe negative root is fixed
by coordinatewise complex conjugation. -/
theorem cubicSecularTrialVector_conj_fixed_of_secularRoot
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot :
      cubicSecularScalar p hL N hprev lam hlam = 0) :
    parityConj p (N + 1)
        (cubicSecularTrialVector p hL N hprev lam hlam) =
      cubicSecularTrialVector p hL N hprev lam hlam := by
  let v :=
    cubicSecularTrialVector p hL N hprev lam hlam
  have hvne : v ≠ 0 := by
    simpa [v] using
      cubicSecularTrialVector_ne_zero p hL N hN hprev lam hlam
  have hveig :
      parityCompressedCanonical p L (N + 1) v =
        (lam : ℂ) • v := by
    simpa [v] using
      (cubicSecularScalar_eq_zero_iff_trial_eigenmode
        p hL N hN hprev lam hlam).mp hroot
  have hconjEig :
      parityCompressedCanonical p L (N + 1)
          (parityConj p (N + 1) v) =
        (lam : ℂ) • parityConj p (N + 1) v := by
    rw [parityCompressedCanonical_conj, hveig]
    apply Subtype.ext
    simp [parityConj, euclideanConj_smul]
  have hconjNe : parityConj p (N + 1) v ≠ 0 := by
    intro hz
    apply hvne
    have hz' := congrArg (parityConj p (N + 1)) hz
    simpa using hz'
  have hk :
      intrinsicCubicQuotientCoordinate p N v = 1 := by
    simpa [v] using
      intrinsicCubicQuotientCoordinate_cubicSecularTrialVector
        p hL N hN hprev lam hlam
  have hkc :
      intrinsicCubicQuotientCoordinate p N
          (parityConj p (N + 1) v) = 1 := by
    have h :=
      intrinsicCubicQuotientCoordinate_conj p N v
    rw [hk] at h
    simpa using h
  have hnormSelf :
      cubicNormalizedSuccessorVector p N
          (parityConj p (N + 1) v) =
        parityConj p (N + 1) v := by
    simp [cubicNormalizedSuccessorVector, hkc]
  have hnorm :
      cubicNormalizedSuccessorVector p N
          (parityConj p (N + 1) v) =
        v := by
    simpa [v] using
      cubicNormalizedSuccessorVector_eq_cubicSecularTrialVector
        p hL N hN hprev hlam hconjNe hconjEig
  exact hnormSelf.symm.trans hnorm

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicSecularTrialVector_conj_fixed_of_secularRoot
