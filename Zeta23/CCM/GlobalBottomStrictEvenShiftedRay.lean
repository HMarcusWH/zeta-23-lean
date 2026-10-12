import Zeta23.CCM.CanonicalShiftedSecular
import Zeta23.CCM.GlobalParityBottomPrimeRemainder
import Zeta23.CCM.RegularFirstBadParitySourceMomentRigidity

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# WP3: the actual #247 selected negative ground on the #287 shifted ray

This is a same-state *identity*, not a positivity or contact exclusion.
The branch hypothesis is explicit: even selected and strictly below odd.
The shift is the negative #247 value, NOT the zero-contact shift.
-/

/-- The exact retained negative bottom lies below the odd floor in the
strict-even branch. -/
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

/-- The successor has the nonzero carrier size required by the shifted ray. -/
theorem GlobalBottomResidualState.two_le_groundSuccessor
    {Q : ℕ} (s : GlobalBottomResidualState Q) :
    2 ≤ s.aligned.firstBad.Nstar + 1 :=
  Nat.succ_le_succ s.aligned.firstBad.one_le_Nstar

/-- Every selected even trial lies on the genuine shifted canonical ray, with
the *actual* source scalar rather than a freely chosen normalization. -/
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

/-- The source scalar of the true selected even trial cannot vanish. -/
theorem GlobalBottomResidualState.evenStrict_trial_source_ne_zero
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    explicitCanonicalSourceMoment s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) s.aligned.evenShiftedTrial ≠ 0 := by
  intro hc
  have ht := s.evenStrict_trial_eq_source_mul_shiftedRay hp hK hlam
  rw [hc, zero_smul] at ht
  exact (s.aligned.evenShiftedTrial_eigenmode_of_even hp).1 ht

/-- Source-normalized shifted ray on exactly the negative ground's spectral
level; the condition H(x)=1 is eigenvalue-equivalent, not RH exclusion. -/
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

/-- The canonical shifted ray is itself an eigenmode at the *negative*
shift, not at the zero-contact spectral parameter. -/
theorem GlobalBottomResidualState.evenStrict_shiftedRay_eigenmode
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    evenCompressedCanonical s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)
      (canonicalShiftedRay s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1) hK hlam) =
      (s.aligned.lam : ℂ) •
        canonicalShiftedRay s.aligned.firstBad.L
          (s.aligned.firstBad.Nstar + 1) hK hlam := by
  have hx := canonical_shifted_apply_ray s.aligned.firstBad.L_pos hK hlam
  rw [s.evenStrict_shiftedRay_source_eq_one hp hK hlam,
      sub_self, zero_smul] at hx
  exact (mem_ker_evenShiftedCanonical_iff _).mp hx

/-- The shifted ray is nonzero because it spans the nonzero ground trial. -/
theorem GlobalBottomResidualState.evenStrict_shiftedRay_ne_zero
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    canonicalShiftedRay s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) hK hlam ≠ 0 := by
  intro hx
  have ht := s.evenStrict_trial_eq_source_mul_shiftedRay hp hK hlam
  rw [hx, smul_zero] at ht
  exact (s.aligned.evenShiftedTrial_eigenmode_of_even hp).1 ht

/-- Exact signed prime remainder + prime-free budget on the negative shifted
ground ray. This follows from the complete physical canonical source;
it excludes no possible negative state. -/
theorem GlobalBottomResidualState.evenStrict_shiftedRay_primeRemainder_budget
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    let x := canonicalShiftedRay s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) hK hlam
    canonicalPrimeRemainderEnergy s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (x : EuclideanSpace ℂ (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) +
      canonicalPrimeFreeBudget s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (x : EuclideanSpace ℂ (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) =
      -s.aligned.lam * ‖x‖ ^ 2 := by
  dsimp
  let x := canonicalShiftedRay s.aligned.firstBad.L
    (s.aligned.firstBad.Nstar + 1) hK hlam
  have heig : evenCompressedCanonical s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) x = (s.aligned.lam : ℂ) • x :=
    s.evenStrict_shiftedRay_eigenmode hp hK hlam
  have henergy : parityCanonicalSourceEnergy .even s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) x = s.aligned.lam * ‖x‖ ^ 2 := by
    unfold parityCanonicalSourceEnergy
    change (inner ℂ
      (evenCompressedCanonical s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1) x) x).re =
      s.aligned.lam * ‖x‖ ^ 2
    rw [heig]
    have hsmul : inner ℂ ((s.aligned.lam : ℂ) • x) x =
        s.aligned.lam • inner ℂ x x := by
      exact inner_smul_real_left (𝕜 := ℂ) x x s.aligned.lam
    rw [hsmul, Complex.smul_re, smul_eq_mul]
    have hnorm : Complex.re (inner ℂ x x) = ‖x‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using
        (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    rw [hnorm]
  have hchannels := parityCanonicalSourceEnergy_eq_channels .even
    s.aligned.firstBad.L_pos (s.aligned.firstBad.Nstar + 1) x
  have hsplit := canonicalSourceChannelEnergy_eq_neg_primeRemainder_sub_budget
    s.aligned.firstBad.L_pos (s.aligned.firstBad.Nstar + 1)
    (x : EuclideanSpace ℂ (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1)))
  rw [← hchannels, henergy] at hsplit
  dsimp [x] at hsplit ⊢
  linarith

/-- Positive defect is a reformulation of negative true-ground energy, not an
independent arithmetic restriction. -/
theorem GlobalBottomResidualState.evenStrict_shiftedRay_budget_pos
    {Q : ℕ} (s : GlobalBottomResidualState Q)
    (hp : s.aligned.firstBad.p = ReversalParity.even)
    (hK : 2 ≤ s.aligned.firstBad.Nstar + 1)
    (hlam : s.aligned.lam < parityRayleighBottom .odd s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1)) :
    let x := canonicalShiftedRay s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) hK hlam
    0 < canonicalPrimeRemainderEnergy s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (x : EuclideanSpace ℂ (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) +
      canonicalPrimeFreeBudget s.aligned.firstBad.L
        (s.aligned.firstBad.Nstar + 1)
        (x : EuclideanSpace ℂ (Fin (2 * (s.aligned.firstBad.Nstar + 1) + 1))) := by
  dsimp
  rw [s.evenStrict_shiftedRay_primeRemainder_budget hp hK hlam]
  have hx : 0 < ‖canonicalShiftedRay s.aligned.firstBad.L
      (s.aligned.firstBad.Nstar + 1) hK hlam‖ ^ 2 := by
    have hn := s.evenStrict_shiftedRay_ne_zero hp hK hlam
    positivity
  have hneg := s.aligned_lam_neg
  nlinarith

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_shift_lt_odd
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_trial_eq_source_mul_shiftedRay
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_trial_source_ne_zero
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_shiftedRay_source_eq_one
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_shiftedRay_eigenmode
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_shiftedRay_primeRemainder_budget
#print axioms Zeta23.CCM.GlobalBottomResidualState.evenStrict_shiftedRay_budget_pos
