import Zeta23.CCM.ParityKernelTower
import Mathlib.Data.Nat.Find

noncomputable section

namespace Zeta23.CCM

open scoped Topology

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

/-- Right-neighborhood stability of the one-step predecessor ground.  At k=1
there is no smaller legal successor index; otherwise the predecessor ground is
nonnegative on some right-neighborhood of the contact. -/
def FirstCrossingPredecessorGroundStable
    (c : CanonicalParityFirstCrossingShell) : Prop :=
  c.k = 1 ∨
    ∃ δ : ℝ, 0 < δ ∧
      ∀ L : ℝ, c.Lstar ≤ L → L < c.Lstar + δ →
        0 ≤ paritySuccessorGround c.p (c.k - 1) L

/-- Minimality of the crossing index gives right-neighborhood predecessor
stability.  If k=n, strict positivity below the minimal zero size plus aperture
continuity gives the neighborhood.  If n<k, failure of predecessor
right-crossing gives it directly. -/
theorem CanonicalParityFirstCrossingShell.predecessorGround_stable
    (c : CanonicalParityFirstCrossingShell) :
    FirstCrossingPredecessorGroundStable c := by
  classical
  by_cases hk1 : c.k = 1
  · exact Or.inl hk1
  · right
    have hk2 : 2 ≤ c.k := by
      have hk1le : 1 ≤ c.k := le_trans c.one_le_n c.n_le_k
      omega
    let j : ℕ := c.k - 1
    have hj1 : 1 ≤ j := by
      dsimp [j]
      omega
    have hjk : j < c.k := by
      dsimp [j]
      omega
    have hjN : j ≤ c.N :=
      le_trans (le_of_lt hjk) c.k_le_N
    by_cases hkn : c.k = c.n
    · have hjn : j < c.n := by
        dsimp [j]
        omega
      have hpos :
          0 < paritySuccessorGround c.p j c.Lstar :=
        c.below_strict_positive j hj1 hjn
      have hstarpos : 0 < c.Lstar :=
        lt_trans c.Lsmall_pos c.Lsmall_lt_Lstar
      have hcontWithin :=
        (continuousOn_parityRayleighBottom_succ_Ioi c.p j hj1)
          c.Lstar hstarpos
      have hcontAt :=
        hcontWithin.continuousAt (isOpen_Ioi.mem_nhds hstarpos)
      have hpre :
          (fun L : ℝ => paritySuccessorGround c.p j L) ⁻¹'
              Set.Ioi (0 : ℝ) ∈ 𝓝 c.Lstar := by
        exact hcontAt.tendsto (isOpen_Ioi.mem_nhds hpos)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
      refine ⟨δ, hδ, ?_⟩
      intro L hLlo hLhi
      have hdist : dist L c.Lstar < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hLlo)]
        linarith
      have hpositive :
          0 < paritySuccessorGround c.p j L :=
        hball (by simpa only [Metric.mem_ball] using hdist)
      simpa [j] using hpositive.le
    · have hnk : c.n < c.k := by
        exact lt_of_le_of_ne c.n_le_k (Ne.symm hkn)
      have hnj : c.n ≤ j := by
        dsimp [j]
        omega
      have hnot :
          ¬ ParityRightCrossesNegative c.p j c.Lstar :=
        c.earlier_plateau_no_right_crossing j hnj hjk
      by_contra hstable
      push_neg at hstable
      apply hnot
      intro ε hε
      obtain ⟨L, hLlo, hLhi, hLneg⟩ := hstable ε hε
      have hjzero :
          paritySuccessorGround c.p j c.Lstar = 0 :=
        c.plateau_zero j hnj hjN
      have hstrict : c.Lstar < L := by
        rcases lt_or_eq_of_le hLlo with h | h
        · exact h
        · subst L
          linarith
      exact ⟨L, hstrict, hLhi, hLneg⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.ParityKernelTower.exists_firstCrossingShell
#print axioms Zeta23.CCM.CanonicalParityFirstCrossingShell.predecessorGround_stable
