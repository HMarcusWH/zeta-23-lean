import Zeta23.CCM.ParityFirstNegativeBoundary
import Zeta23.CCM.CanonicalGroundContinuity
import Zeta23.CCM.GlobalParityBottomContactNormalForm
import Mathlib.Topology.Order.Compact

noncomputable section

namespace Zeta23.CCM

open Set
open scoped Topology

/-!
# Post-#281 global first-negative boundary

This is the global-minimum analogue of `ParityFirstNegativeBoundary`.  It is
constructed from the exact fixed-N global successor bottom, not from a selected
parity.  The boundary is the least point in the closure of the negative set on
one compact positive/negative bracket.  Earlier zero tangencies are permitted:
this is the first *negative boundary*, not the first zero.

No aperture monotonicity, crossing barrier, or RH premise is used.
-/

/-- Negative global-bottom values occur arbitrarily close to the right. -/
def GlobalRightCrossesNegative
    (N : ℕ) (Lstar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ L : ℝ,
      Lstar < L ∧
      L < Lstar + ε ∧
      globalParitySuccessorBottom L N < 0

/-- The first boundary of the fixed-N negative global-bottom set after a
positive anchor. -/
structure GlobalParityFirstNegativeBoundary where
  N : ℕ
  one_le_N : 1 ≤ N
  Lsmall : ℝ
  Lstar : ℝ
  Lneg : ℝ
  Lsmall_pos : 0 < Lsmall
  Lsmall_lt_Lstar : Lsmall < Lstar
  Lstar_lt_Lneg : Lstar < Lneg
  base_positive :
    0 < globalParitySuccessorBottom Lsmall N
  contact_zero :
    globalParitySuccessorBottom Lstar N = 0
  prefix_nonnegative :
    ∀ L : ℝ, Lsmall ≤ L → L ≤ Lstar →
      0 ≤ globalParitySuccessorBottom L N
  right_crossing :
    GlobalRightCrossesNegative N Lstar

/-- A fixed-N positive/negative global bracket produces its genuine first
negative boundary. -/
theorem exists_globalParityFirstNegativeBoundary_of_signOpposition
    {N : ℕ} (hN : 1 ≤ N)
    {Lsmall Lneg : ℝ}
    (hLsmall : 0 < Lsmall)
    (hLt : Lsmall < Lneg)
    (hbase : 0 < globalParitySuccessorBottom Lsmall N)
    (hneg : globalParitySuccessorBottom Lneg N < 0) :
    ∃ c : GlobalParityFirstNegativeBoundary,
      c.N = N ∧ c.Lsmall = Lsmall ∧ c.Lneg = Lneg := by
  let g : ℝ → ℝ := fun L => globalParitySuccessorBottom L N
  let S : Set ℝ := {L | L ∈ Icc Lsmall Lneg ∧ g L < 0}
  let C : Set ℝ := closure S

  have hSne : S.Nonempty := by
    refine ⟨Lneg, ?_⟩
    exact ⟨⟨le_of_lt hLt, le_rfl⟩, by simpa [g] using hneg⟩
  have hSsub : S ⊆ Icc Lsmall Lneg := by
    intro L hL
    exact hL.1
  have hCsub : C ⊆ Icc Lsmall Lneg := by
    dsimp [C]
    exact closure_minimal hSsub isClosed_Icc
  have hCcompact : IsCompact C :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hCsub
  have hCne : C.Nonempty :=
    hSne.mono (fun _ h => subset_closure h)

  let Lstar : ℝ := sInf C
  have hleast : IsLeast C Lstar := by
    dsimp [Lstar]
    exact hCcompact.isLeast_sInf hCne
  have hstarC : Lstar ∈ C := hleast.1
  have hstarIcc : Lstar ∈ Icc Lsmall Lneg := hCsub hstarC
  have hstarpos : 0 < Lstar := lt_of_lt_of_le hLsmall hstarIcc.1
  have hcontAt : ContinuousAt g Lstar := by
    have hwithin :=
      (continuousOn_globalParitySuccessorBottom_Ioi N hN)
        Lstar hstarpos
    exact hwithin.continuousAt (isOpen_Ioi.mem_nhds hstarpos)

  have hstar_nonpos : g Lstar ≤ 0 := by
    by_contra hnot
    have hpos : 0 < g Lstar := lt_of_not_ge hnot
    have hpre : g ⁻¹' Ioi (0 : ℝ) ∈ 𝓝 Lstar :=
      hcontAt.tendsto (isOpen_Ioi.mem_nhds hpos)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hmeet :=
      (mem_closure_iff.mp hstarC)
        (Metric.ball Lstar δ) Metric.isOpen_ball
        (Metric.mem_ball_self hδ)
    obtain ⟨x, hxball, hxS⟩ := hmeet
    have hxpos : 0 < g x := hball hxball
    have hxneg : g x < 0 := by
      change x ∈ Icc Lsmall Lneg ∧ g x < 0 at hxS
      exact hxS.2
    linarith

  have hsmallstar : Lsmall < Lstar := by
    rcases lt_or_eq_of_le hstarIcc.1 with h | h
    · exact h
    · have hnonposSmall : g Lsmall ≤ 0 := by
        rw [h]
        exact hstar_nonpos
      have hb : 0 < g Lsmall := by simpa [g] using hbase
      linarith

  have hstar_nonneg : 0 ≤ g Lstar := by
    by_contra hnot
    have hnegstar : g Lstar < 0 := lt_of_not_ge hnot
    have hpre : g ⁻¹' Iio (0 : ℝ) ∈ 𝓝 Lstar :=
      hcontAt.tendsto (isOpen_Iio.mem_nhds hnegstar)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
    let η : ℝ := min δ (Lstar - Lsmall)
    have hη : 0 < η := lt_min hδ (sub_pos.mpr hsmallstar)
    let x : ℝ := Lstar - η / 2
    have hxlt : x < Lstar := by
      dsimp [x]
      linarith
    have hxsmall : Lsmall ≤ x := by
      have hηle : η ≤ Lstar - Lsmall := min_le_right _ _
      dsimp [x]
      linarith
    have hxneg : g x < 0 := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have hsub : x - Lstar = -(η / 2) := by
        dsimp [x]
        ring
      rw [hsub, abs_neg, abs_of_pos (by linarith : 0 < η / 2)]
      have hηle : η ≤ δ := min_le_left _ _
      linarith
    have hxS : x ∈ S := by
      refine ⟨⟨hxsmall, ?_⟩, hxneg⟩
      exact le_trans (le_of_lt hxlt) hstarIcc.2
    have hstar_le_x : Lstar ≤ x := hleast.2 (subset_closure hxS)
    linarith

  have hcontact : g Lstar = 0 := by linarith
  have hstarlneg : Lstar < Lneg := by
    rcases lt_or_eq_of_le hstarIcc.2 with h | h
    · exact h
    · have hzeroNeg : g Lneg = 0 := by
        rw [← h]
        exact hcontact
      have hn : g Lneg < 0 := by simpa [g] using hneg
      linarith

  have hprefix :
      ∀ L : ℝ, Lsmall ≤ L → L ≤ Lstar → 0 ≤ g L := by
    intro L hLsmallL hLLstar
    by_contra hnot
    have hLneg : g L < 0 := lt_of_not_ge hnot
    have hLS : L ∈ S := by
      refine ⟨⟨hLsmallL, ?_⟩, hLneg⟩
      exact le_trans hLLstar (le_of_lt hstarlneg)
    have hstar_le_L : Lstar ≤ L := hleast.2 (subset_closure hLS)
    have hEq : L = Lstar := le_antisymm hLLstar hstar_le_L
    subst L
    linarith

  have hright : GlobalRightCrossesNegative N Lstar := by
    intro ε hε
    have hmeet :=
      (mem_closure_iff.mp hstarC)
        (Metric.ball Lstar ε) Metric.isOpen_ball
        (Metric.mem_ball_self hε)
    obtain ⟨L, hLball, hLS⟩ := hmeet
    have hLneg : g L < 0 := by
      change L ∈ Icc Lsmall Lneg ∧ g L < 0 at hLS
      exact hLS.2
    have hstar_le_L : Lstar ≤ L := hleast.2 (subset_closure hLS)
    have hne : L ≠ Lstar := by
      intro hEq
      subst L
      linarith
    have hstar_lt_L : Lstar < L := lt_of_le_of_ne hstar_le_L hne.symm
    have hdist : dist L Lstar < ε := by
      simpa only [Metric.mem_ball] using hLball
    have hLupper : L < Lstar + ε := by
      rw [Real.dist_eq, abs_lt] at hdist
      linarith
    exact ⟨L, hstar_lt_L, hLupper, by simpa [g] using hLneg⟩

  let c : GlobalParityFirstNegativeBoundary := {
    N := N
    one_le_N := hN
    Lsmall := Lsmall
    Lstar := Lstar
    Lneg := Lneg
    Lsmall_pos := hLsmall
    Lsmall_lt_Lstar := hsmallstar
    Lstar_lt_Lneg := hstarlneg
    base_positive := hbase
    contact_zero := by simpa [g] using hcontact
    prefix_nonnegative := by
      intro L h1 h2
      simpa [g] using hprefix L h1 h2
    right_crossing := hright
  }
  exact ⟨c, rfl, rfl, rfl⟩

/-- The exact even/tie/odd trichotomy at the global boundary. -/
theorem GlobalParityFirstNegativeBoundary.parityBranch
    (c : GlobalParityFirstNegativeBoundary) :
    ZeroContactParityBranch c.Lstar c.N :=
  zeroContactParityBranch_of_globalParitySuccessorBottom_eq_zero c.contact_zero

/-- Global-prefix nonnegativity implies nonnegativity of each parity separately
at the same terminal cutoff. -/
theorem GlobalParityFirstNegativeBoundary.prefix_eachParity_nonnegative
    (c : GlobalParityFirstNegativeBoundary)
    (p : ReversalParity)
    {L : ℝ}
    (hsmall : c.Lsmall ≤ L)
    (hstar : L ≤ c.Lstar) :
    0 ≤ paritySuccessorGround p c.N L := by
  have hglobal := c.prefix_nonnegative L hsmall hstar
  unfold globalParitySuccessorBottom at hglobal
  cases p with
  | even => exact le_trans hglobal (min_le_left _ _)
  | odd => exact le_trans hglobal (min_le_right _ _)

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_globalParityFirstNegativeBoundary_of_signOpposition
#print axioms Zeta23.CCM.GlobalParityFirstNegativeBoundary.parityBranch
#print axioms Zeta23.CCM.GlobalParityFirstNegativeBoundary.prefix_eachParity_nonnegative
