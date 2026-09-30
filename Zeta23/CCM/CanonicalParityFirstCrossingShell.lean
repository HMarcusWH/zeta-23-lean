import Zeta23.CCM.ParityKernelTower
import Mathlib.Data.Nat.Find

noncomputable section

namespace Zeta23.CCM

/-!
# Post-#278 canonical parity first-crossing shell

The terminal parity is negative arbitrarily close to the right of the aperture
contact.  Inside the zero plateau we now choose the least truncation index with
that outgoing-negative behavior.

This is the exact N-flow localization needed before one-step Schur analysis:
all earlier plateau indices fail to right-cross negative, while the selected
successor index does.

The definition does not yet assert that the inherited zero mode itself uses the
new shell.  That stronger statement would be false in general; the dynamical
one-step crossing is the object retained here.
-/

/-- A zero-kernel tower together with the least plateau index whose parity
bottom becomes negative arbitrarily close to the right of the contact. -/
structure CanonicalParityFirstCrossingShell extends ParityKernelTower where
  k : ℕ
  n_le_k : n ≤ k
  k_le_N : k ≤ N
  successor_right_crossing :
    ParityRightCrossesNegative p k Lstar
  earlier_plateau_no_right_crossing :
    ∀ m : ℕ, n ≤ m → m < k →
      ¬ ParityRightCrossesNegative p m Lstar

/-- Every kernel tower ends at a right-crossing terminal index, so a least
right-crossing index exists inside the zero plateau. -/
theorem ParityKernelTower.exists_firstCrossingShell
    (t : ParityKernelTower) :
    ∃ c : CanonicalParityFirstCrossingShell,
      c.toParityKernelTower = t := by
  classical
  let P : ℕ → Prop := fun m =>
    t.n ≤ m ∧ m ≤ t.N ∧
      ParityRightCrossesNegative t.p m t.Lstar
  have hP : ∃ m : ℕ, P m := by
    exact ⟨t.N, t.n_le_N, le_rfl, t.right_crossing⟩
  let k : ℕ := Nat.find hP
  have hkP : P k := Nat.find_spec hP
  have hnk : t.n ≤ k := hkP.1
  have hkN : k ≤ t.N := hkP.2.1
  have hkcross :
      ParityRightCrossesNegative t.p k t.Lstar := hkP.2.2
  have hearlier :
      ∀ m : ℕ, t.n ≤ m → m < k →
        ¬ ParityRightCrossesNegative t.p m t.Lstar := by
    intro m hnm hmk hcross
    have hmN : m ≤ t.N := le_trans (le_of_lt hmk) hkN
    exact Nat.find_min hP hmk ⟨hnm, hmN, hcross⟩
  let c : CanonicalParityFirstCrossingShell := {
    toParityKernelTower := t
    k := k
    n_le_k := hnk
    k_le_N := hkN
    successor_right_crossing := hkcross
    earlier_plateau_no_right_crossing := hearlier
  }
  exact ⟨c, rfl⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.ParityKernelTower.exists_firstCrossingShell
