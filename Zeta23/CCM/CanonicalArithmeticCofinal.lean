import Zeta23.CCM.CanonicalArithmeticLowerBound
import Zeta23.CCM.CofinalLowerBound

noncomputable section

namespace Zeta23.CCM

/-!
# Cofinal canonical arithmetic certificates

This module connects the exact all-vector arithmetic certificate to the
already-proved cofinal order mechanism.  It does not construct such a family.
-/

/-- At one positive aperture, arbitrarily large finite sizes admit arbitrarily
small all-vector canonical arithmetic lower certificates, with size and error
jointly quantified. -/
def JointCofinalCanonicalArithmeticLowerBounds (L : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε →
    ∃ m : ℕ, n ≤ m ∧ CanonicalArithmeticLowerBound L (m + 1) ε

/-- The arithmetic family supplies the abstract bottom-level cofinal
certificates used by the antitone N-flow argument. -/
theorem jointCofinalBottomLowerBounds_of_jointCofinalCanonicalArithmeticLowerBounds
    {L : ℝ} (hL : 0 < L)
    (hcert : JointCofinalCanonicalArithmeticLowerBounds L) :
    JointCofinalBottomLowerBounds L := by
  intro n hn ε hε
  obtain ⟨m, hnm, hm⟩ := hcert n hn ε hε
  refine ⟨m, hnm, ?_⟩
  exact globalParitySuccessorBottom_lowerBound_of_canonicalArithmeticLowerBound
    hL m (by omega) ε hm

/-- Therefore every finite successor bottom at that aperture is nonnegative. -/
theorem globalParitySuccessorBottom_nonneg_of_jointCofinalCanonicalArithmeticLowerBounds
    {L : ℝ} (hL : 0 < L)
    (hcert : JointCofinalCanonicalArithmeticLowerBounds L) :
    ∀ n : ℕ, 1 ≤ n → 0 ≤ globalParitySuccessorBottom L n := by
  exact globalParitySuccessorBottom_nonneg_of_jointCofinal_lowerBounds
    hL
    (jointCofinalBottomLowerBounds_of_jointCofinalCanonicalArithmeticLowerBounds
      hL hcert)

end Zeta23.CCM

#print axioms Zeta23.CCM.jointCofinalBottomLowerBounds_of_jointCofinalCanonicalArithmeticLowerBounds
#print axioms Zeta23.CCM.globalParitySuccessorBottom_nonneg_of_jointCofinalCanonicalArithmeticLowerBounds
