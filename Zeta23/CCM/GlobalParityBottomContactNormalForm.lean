import Zeta23.CCM.GlobalParityBottomFirstContact
import Zeta23.CCM.GoodSectorKernelAnnihilation
import Zeta23.CCM.CanonicalApertureRegularityScaffold
import Zeta23.CCM.GlobalParityBottomSimplicity

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#277 zero-contact normal form

At an exact global contact the common legal ground is zero.  Therefore neither
successor parity can be bad, and the existing parity trichotomy becomes an
exact even-strict / tie / odd-strict zero-contact classification.

Predecessor geometry is classified by the repository's existing
IntrinsicPredecessorRegular predicate.  No WLOG-even reduction, inverse in a
singular branch, or ambient-kernel claim is introduced.
-/

/-- Exact parity geometry at a zero global successor ground. -/
inductive ZeroContactParityBranch (L : ℝ) (N : ℕ) : Prop
  | evenStrict
      (even_zero : parityRayleighBottom .even L (N + 1) = 0)
      (odd_pos : 0 < parityRayleighBottom .odd L (N + 1))
  | tie
      (even_zero : parityRayleighBottom .even L (N + 1) = 0)
      (odd_zero : parityRayleighBottom .odd L (N + 1) = 0)
  | oddStrict
      (odd_zero : parityRayleighBottom .odd L (N + 1) = 0)
      (even_pos : 0 < parityRayleighBottom .even L (N + 1))

/-- A zero global bottom excludes successor badness in either parity. -/
theorem not_anyParityBad_of_globalParitySuccessorBottom_eq_zero
    {L : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hzero : globalParitySuccessorBottom L N = 0) :
    ¬ AnyParityBad L (N + 1) := by
  intro hbad
  have hneg := globalParitySuccessorBottom_neg_of_anyParityBad hbad
  rw [hzero] at hneg
  exact (lt_irrefl 0) hneg

theorem not_evenParityBad_of_globalParitySuccessorBottom_eq_zero
    {L : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hzero : globalParitySuccessorBottom L N = 0) :
    ¬ ParityBad .even L (N + 1) := by
  intro hbad
  exact
    (not_anyParityBad_of_globalParitySuccessorBottom_eq_zero hN hzero)
      (Or.inl hbad)

theorem not_oddParityBad_of_globalParitySuccessorBottom_eq_zero
    {L : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hzero : globalParitySuccessorBottom L N = 0) :
    ¬ ParityBad .odd L (N + 1) := by
  intro hbad
  exact
    (not_anyParityBad_of_globalParitySuccessorBottom_eq_zero hN hzero)
      (Or.inr hbad)

/-- The ordinary parity trichotomy sharpens to an exact zero-contact normal
form.  Strict branches have a positive opposite-parity gap; a tie has two zero
parity grounds. -/
theorem zeroContactParityBranch_of_globalParitySuccessorBottom_eq_zero
    {L : ℝ} {N : ℕ}
    (hzero : globalParitySuccessorBottom L N = 0) :
    ZeroContactParityBranch L N := by
  rcases paritySuccessorBottom_trichotomy L N with hstrict | htie | hstrict
  · have heven :
        parityRayleighBottom .even L (N + 1) = 0 := by
      rw [globalParitySuccessorBottom, min_eq_left (le_of_lt hstrict)] at hzero
      exact hzero
    have hodd :
        0 < parityRayleighBottom .odd L (N + 1) := by
      rw [← heven]
      exact hstrict
    exact .evenStrict heven hodd
  · have heven :
        parityRayleighBottom .even L (N + 1) = 0 := by
      have hzero' := hzero
      rw [globalParitySuccessorBottom,
        min_eq_left (le_of_eq htie)] at hzero'
      exact hzero'
    have hodd :
        parityRayleighBottom .odd L (N + 1) = 0 :=
      htie.symm.trans heven
    exact .tie heven hodd
  · have hodd :
        parityRayleighBottom .odd L (N + 1) = 0 := by
      rw [globalParitySuccessorBottom, min_eq_right (le_of_lt hstrict)] at hzero
      exact hzero
    have heven :
        0 < parityRayleighBottom .even L (N + 1) := by
      rw [← hodd]
      exact hstrict
    exact .oddStrict hodd heven

/-- Contact predecessor geometry uses the existing singular-safe repository
predicate rather than a new spectral notion. -/
inductive ZeroContactPredecessorBranch
    (p : ReversalParity) (L : ℝ) (N : ℕ) : Prop
  | regular (hreg : IntrinsicPredecessorRegular p L N)
  | singular (hsing : ¬ IntrinsicPredecessorRegular p L N)

theorem zeroContactPredecessorBranch
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    ZeroContactPredecessorBranch p L N := by
  classical
  by_cases hreg : IntrinsicPredecessorRegular p L N
  · exact .regular hreg
  · exact .singular hreg

end Zeta23.CCM

#print axioms Zeta23.CCM.not_anyParityBad_of_globalParitySuccessorBottom_eq_zero
#print axioms Zeta23.CCM.zeroContactParityBranch_of_globalParitySuccessorBottom_eq_zero
#print axioms Zeta23.CCM.zeroContactPredecessorBranch
