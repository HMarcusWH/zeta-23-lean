import Zeta23.CCM.ParityFirstNegativeBoundary
import Zeta23.CCM.GlobalParityBottomNFlow
import Mathlib.Data.Nat.Find

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 parity zero plateau

At a one-parity first-negative boundary the terminal successor bottom is zero.
Fixed-aperture N-flow antitonicity then forces every smaller legal truncation
bottom to be nonnegative.  Selecting the least legal index with zero bottom
therefore produces a strict-positive prefix followed by an exact finite
zero plateau.

This is N-flow geometry only.  It does not assert any aperture monotonicity or
exclude the outgoing negative branch.
-/

/-- Least-zero-size package inside one fixed-parity first-negative boundary. -/
structure ParityZeroPlateau extends ParityFirstNegativeBoundary where
  n : ℕ
  one_le_n : 1 ≤ n
  n_le_N : n ≤ N
  minimal_zero :
    paritySuccessorGround p n Lstar = 0
  below_strict_positive :
    ∀ m : ℕ, 1 ≤ m → m < n →
      0 < paritySuccessorGround p m Lstar
  plateau_zero :
    ∀ m : ℕ, n ≤ m → m ≤ N →
      paritySuccessorGround p m Lstar = 0

/-- Every first-negative boundary contains a least zero truncation and hence an
exact N-flow zero plateau ending at the terminal crossing index. -/
theorem ParityFirstNegativeBoundary.exists_zeroPlateau
    (c : ParityFirstNegativeBoundary) :
    ∃ z : ParityZeroPlateau,
      z.toParityFirstNegativeBoundary = c := by
  classical
  let P : ℕ → Prop := fun m =>
    1 ≤ m ∧ m ≤ c.N ∧
      paritySuccessorGround c.p m c.Lstar = 0
  have hP : ∃ m : ℕ, P m := by
    refine ⟨c.N, c.one_le_N, le_rfl, ?_⟩
    exact c.contact_zero
  let n : ℕ := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  have hn1 : 1 ≤ n := hnP.1
  have hnN : n ≤ c.N := hnP.2.1
  have hnzero :
      paritySuccessorGround c.p n c.Lstar = 0 := hnP.2.2

  have hterminalNonneg :
      ∀ m : ℕ, 1 ≤ m → m ≤ c.N →
        0 ≤ paritySuccessorGround c.p m c.Lstar := by
    intro m hm hmN
    have hanti :=
      parityRayleighBottom_succ_antitone_of_le
        c.p
        (lt_trans c.Lsmall_pos c.Lsmall_lt_Lstar)
        hm hmN
    change
      paritySuccessorGround c.p c.N c.Lstar ≤
        paritySuccessorGround c.p m c.Lstar at hanti
    rw [c.contact_zero] at hanti
    exact hanti

  have hbelow :
      ∀ m : ℕ, 1 ≤ m → m < n →
        0 < paritySuccessorGround c.p m c.Lstar := by
    intro m hm hmn
    have hmN : m ≤ c.N := le_trans (le_of_lt hmn) hnN
    have hnonneg := hterminalNonneg m hm hmN
    have hne :
        paritySuccessorGround c.p m c.Lstar ≠ 0 := by
      intro hzero
      have hmP : P m := ⟨hm, hmN, hzero⟩
      exact Nat.find_min hP hmn hmP
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

  have hplateau :
      ∀ m : ℕ, n ≤ m → m ≤ c.N →
        paritySuccessorGround c.p m c.Lstar = 0 := by
    intro m hnm hmN
    have hm1 : 1 ≤ m := le_trans hn1 hnm
    have hlower := hterminalNonneg m hm1 hmN
    have hupper :=
      parityRayleighBottom_succ_antitone_of_le
        c.p
        (lt_trans c.Lsmall_pos c.Lsmall_lt_Lstar)
        hn1 hnm
    change
      paritySuccessorGround c.p m c.Lstar ≤
        paritySuccessorGround c.p n c.Lstar at hupper
    rw [hnzero] at hupper
    exact le_antisymm hupper hlower

  let z : ParityZeroPlateau := {
    toParityFirstNegativeBoundary := c
    n := n
    one_le_n := hn1
    n_le_N := hnN
    minimal_zero := hnzero
    below_strict_positive := hbelow
    plateau_zero := hplateau
  }
  exact ⟨z, rfl⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.ParityFirstNegativeBoundary.exists_zeroPlateau
