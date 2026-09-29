import Zeta23.CCM.ParityRayleighPerturbation

noncomputable section

namespace Zeta23.CCM

open Set

/-!
# Post-#277 fixed-N legal-ground continuity interface

PR #277 proves fixed-N sign opposition under a hypothetical off-line zeta zero.
The remaining subterminal topology gate is continuity in aperture of the exact
legal successor ground.

This file names that gate without assuming simplicity, choosing an eigenbranch,
or importing any RH premise.  The production proof must ultimately discharge
this proposition from the exact canonical matrix through fixed cutoff cells and
all logarithmic cutoff seams.
-/

/-- Exact continuity obligation for every nontrivial fixed successor index. -/
def CanonicalFixedNGroundContinuity : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ContinuousOn
      (fun L : ℝ => globalParitySuccessorBottom L N)
      (Ioi (0 : ℝ))

/-- Registry/downstream-facing eliminator for the fixed-N continuity
interface.  This theorem does not prove the interface. -/
theorem continuousOn_globalParitySuccessorBottom_Ioi_of_fixedN
    (h : CanonicalFixedNGroundContinuity)
    (N : ℕ) (hN : 1 ≤ N) :
    ContinuousOn
      (fun L : ℝ => globalParitySuccessorBottom L N)
      (Ioi (0 : ℝ)) :=
  h N hN

end Zeta23.CCM

#print axioms Zeta23.CCM.continuousOn_globalParitySuccessorBottom_Ioi_of_fixedN
