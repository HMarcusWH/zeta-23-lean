import Zeta23.CCM.GlobalParityBottomResidualState
import Zeta23.CCM.CubicExplicitSecular
import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.RegularFirstBadCrossParityRiesz

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — true global-ground trial

The aligned certificate already stores the exact global-bottom shift.  Its
canonical cubic secular trial is therefore the genuine selected ground
eigenmode.  This module derives that vector rather than storing a duplicate
field, and carries its negative energy directly into the production channel
decomposition.
-/

/-- Canonical cubic trial at the globally aligned retained shift. -/
def GlobalBottomResidualState.groundTrial
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    euclideanParityBoundaryFlatSubspace
      s.aligned.firstBad.p (s.aligned.firstBad.Nstar + 1) :=
  cubicSecularTrialVector
    s.aligned.firstBad.p
    s.aligned.firstBad.L_pos
    s.aligned.firstBad.Nstar
    s.aligned.predecessorNonnegative
    s.aligned.lam
    s.aligned.lam_neg

/-- On an even-selected branch, the true global-ground trial is exactly the
same ambient vector as the retained even shifted trial used by the source/M4
geometry.  Proof-valued predecessor-nonnegativity arguments do not create a
second mathematical vector. -/
theorem GlobalBottomResidualState.groundTrial_coe_eq_evenShiftedTrial_of_even
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even) :
    (s.groundTrial : EuclideanSpace ℂ
      (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) =
      (s.aligned.evenShiftedTrial : EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) := by
  change
    ((cubicSecularTrialVector
      s.aligned.firstBad.p
      s.aligned.firstBad.L_pos
      s.aligned.firstBad.Nstar
      s.aligned.predecessorNonnegative
      s.aligned.lam
      s.aligned.lam_neg :
        euclideanParityBoundaryFlatSubspace
          s.aligned.firstBad.p (s.aligned.firstBad.Nstar + 1)) :
      EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) =
    ((cubicSecularTrialVector
      .even
      s.aligned.firstBad.L_pos
      s.aligned.firstBad.Nstar
      (s.aligned.firstBad.predecessorNonnegative_anyParity .even)
      s.aligned.lam
      s.aligned.lam_neg :
        euclideanEvenBoundaryFlatSubspace
          (s.aligned.firstBad.Nstar + 1)) :
      EuclideanSpace ℂ
        (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))
  rw [hp]

/-- The globally aligned cubic trial is nonzero. -/
theorem GlobalBottomResidualState.groundTrial_ne_zero
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    s.groundTrial ≠ 0 := by
  simpa [GlobalBottomResidualState.groundTrial] using
    cubicSecularTrialVector_ne_zero
      s.aligned.firstBad.p
      s.aligned.firstBad.L_pos
      s.aligned.firstBad.Nstar
      s.aligned.firstBad.one_le_Nstar
      s.aligned.predecessorNonnegative
      s.aligned.lam
      s.aligned.lam_neg

/-- The derived trial is an exact eigenmode at the stored global bottom. -/
theorem GlobalBottomResidualState.groundTrial_eigenmode
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    parityCompressedCanonical s.aligned.firstBad.p
        s.aligned.firstBad.L (s.aligned.firstBad.Nstar + 1)
        s.groundTrial =
      (s.aligned.lam : ℂ) • s.groundTrial := by
  have h :=
    (cubicExplicitSchurScalar_eq_zero_iff_trial_eigenmode
      s.aligned.firstBad.p
      s.aligned.firstBad.L_pos
      s.aligned.firstBad.Nstar
      s.aligned.firstBad.one_le_Nstar
      s.aligned.predecessorNonnegative
      s.aligned.lam
      s.aligned.lam_neg).mp
      s.aligned.explicit_root
  simpa [GlobalBottomResidualState.groundTrial] using h

/-- Exact Rayleigh energy of the selected global ground trial. -/
theorem GlobalBottomResidualState.groundTrial_parityEnergy_eq
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    parityCanonicalSourceEnergy s.aligned.firstBad.p
        s.aligned.firstBad.L (s.aligned.firstBad.Nstar + 1)
        s.groundTrial =
      s.aligned.lam * ‖s.groundTrial‖ ^ 2 := by
  unfold parityCanonicalSourceEnergy
  rw [s.groundTrial_eigenmode]
  have hsmul :
      inner ℂ ((s.aligned.lam : ℂ) • s.groundTrial) s.groundTrial =
        s.aligned.lam • inner ℂ s.groundTrial s.groundTrial := by
    exact inner_smul_real_left (𝕜 := ℂ)
      s.groundTrial s.groundTrial s.aligned.lam
  rw [hsmul, Complex.smul_re, smul_eq_mul]
  have hnorm :
      Complex.re (inner ℂ s.groundTrial s.groundTrial) =
        ‖s.groundTrial‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) s.groundTrial).symm
  rw [hnorm]

/-- The true selected global ground trial has strictly negative canonical
parity energy. -/
theorem GlobalBottomResidualState.groundTrial_parityEnergy_neg
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    parityCanonicalSourceEnergy s.aligned.firstBad.p
        s.aligned.firstBad.L (s.aligned.firstBad.Nstar + 1)
        s.groundTrial < 0 := by
  rw [s.groundTrial_parityEnergy_eq]
  have hnorm : 0 < ‖s.groundTrial‖ ^ 2 := by
    have h : 0 < ‖s.groundTrial‖ := norm_pos_iff.mpr s.groundTrial_ne_zero
    positivity
  exact mul_neg_of_neg_of_pos s.aligned.lam_neg hnorm

/-- The same true ground vector has strictly negative complete source-channel
energy. -/
theorem GlobalBottomResidualState.groundTrial_channelEnergy_neg
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    canonicalSourceChannelEnergy
        s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (s.groundTrial : EuclideanSpace ℂ
          (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) < 0 := by
  rw [← parityCanonicalSourceEnergy_eq_channels
    s.aligned.firstBad.p s.aligned.firstBad.L_pos
    (s.aligned.firstBad.Nstar + 1) s.groundTrial]
  exact s.groundTrial_parityEnergy_neg

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_coe_eq_evenShiftedTrial_of_even
#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_ne_zero
#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_eigenmode
#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_parityEnergy_eq
#print axioms Zeta23.CCM.GlobalBottomResidualState.groundTrial_channelEnergy_neg
