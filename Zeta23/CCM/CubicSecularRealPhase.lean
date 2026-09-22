import Zeta23.CCM.CubicSecularRealGeometry

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Canonical cubic secular real phase

The canonical cubic trial is now known to be fixed by coordinate conjugation
for every safe real negative shift, before any secular-root condition is
imposed.  The historical root-specific theorem is retained as a compatibility
interface for downstream code.

No sign, branch exclusion, negative-root exclusion, or RH claim is asserted.
-/

/-- Compatibility corollary: a canonical cubic secular trial at a genuine safe
negative root is fixed by coordinatewise complex conjugation. -/
theorem cubicSecularTrialVector_conj_fixed_of_secularRoot
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (_hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (_hroot :
      cubicSecularScalar p hL N hprev lam hlam = 0) :
    parityConj p (N + 1)
        (cubicSecularTrialVector p hL N hprev lam hlam) =
      cubicSecularTrialVector p hL N hprev lam hlam := by
  exact cubicSecularTrialVector_conj_fixed p hL N hprev lam hlam

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicSecularTrialVector_conj_fixed_of_secularRoot
