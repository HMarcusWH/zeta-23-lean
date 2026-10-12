import Zeta23.CCM.CanonicalShiftedSecular
import Zeta23.CCM.GlobalParityBottomPrimeRemainder

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# WP3 — the exact #247 selected ground in the #287 shifted coordinates

Only the strict-even branch is covered; the shift is the actual selected
negative eigenvalue, not the zero-contact specialization. The following
identities contain no independent signed-arithmetic exclusion.
-/

/-- The global lowest eigenvalue is below the odd bottom in strict-even. -/
theorem GlobalBottomResidualState.evenStrict_shift_lt_odd
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hstrict : parityRayleighBottom .even s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1) <
      parityRayleighBottom .odd s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)) :
    s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) := by
  have hglobal : s.aligned.lam =
      parityRayleighBottom .even s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1) := by
    rw [s.aligned_lam_is_global, globalParitySuccessorBottom,
      min_eq_left (le_of_lt hstrict)]
  exact lt_of_eq_of_lt hglobal hstrict

/-- The selected successor has legal index at least two. -/
theorem GlobalBottomResidualState.two_le_groundSuccessor
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    2 ≤ s.aligned.firstBad.Nstar + 1 :=
  Nat.succ_le_succ s.aligned.firstBad.one_le_Nstar

/-- Same-state shifted ray (Step 64 applied to the genuine #247 trial). -/
theorem GlobalBottomResidualState.evenStrict_trial_eq_source_mul_shiftedRay
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    s.aligned.evenShiftedTrial =
      explicitCanonicalSourceMoment s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1) s.aligned.evenShiftedTrial •
        canonicalShiftedRay s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1) hK hlam := by
  exact canonical_shifted_eigenvector_eq_smul
    s.aligned.firstBad.L_pos hK hlam
    (s.aligned.evenShiftedTrial_eigenmode_of_even hp).2

/-- Nonvanishing of the genuine selected trial's source coefficient. -/
theorem GlobalBottomResidualState.evenStrict_trial_source_ne_zero
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    explicitCanonicalSourceMoment s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) s.aligned.evenShiftedTrial ≠ 0 := by
  intro hc
  have htrial := s.evenStrict_trial_eq_source_mul_shiftedRay hp hK hlam
  rw [hc, zero_smul] at htrial
  exact (s.aligned.evenShiftedTrial_eigenmode_of_even hp).1 htrial

/-- The associated negative-shift resolvent ray is source-normalized to one. -/
theorem GlobalBottomResidualState.evenStrict_shiftedRay_source_eq_one
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    explicitCanonicalSourceMoment s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)
      (canonicalShiftedRay s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1) hK hlam) = 1 := by
  apply (canonical_shifted_eigen_iff
    s.aligned.firstBad.L_pos hK hlam).2
  exact ⟨s.aligned.evenShiftedTrial,
    (s.aligned.evenShiftedTrial_eigenmode_of_even hp).1,
    (s.aligned.evenShiftedTrial_eigenmode_of_even hp).2⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_shift_lt_odd
#print axioms Zeta23.CCM.GlobalBottomResidualState.two_le_groundSuccessor
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_trial_eq_source_mul_shiftedRay
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_trial_source_ne_zero
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_shiftedRay_source_eq_one
