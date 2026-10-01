import Zeta23.CCM.CanonicalGroundContinuity
import Mathlib.Topology.Order.Compact

noncomputable section

namespace Zeta23.CCM

open Set
open scoped Topology

/-!
# Post-#278 parity first-negative boundary

The global legal successor bottom is the minimum of the even and odd parity
bottoms.  Once a terminal negative parity is selected, the closure route stays
on that parity rather than repeatedly reasoning through the minimum.

The first-boundary theorem below takes one fixed parity with a positive anchor,
a later negative value, and the already-proved production continuity theorem.
It selects the least point in the closure of the negative set on the compact
bracketing interval.  This gives an exact zero, a nonnegative prefix, and
negative values arbitrarily close on the right.

No aperture monotonicity, crossing barrier, or RH premise is used.
-/

/-- The successor parity bottom at predecessor-size index `N`. -/
def paritySuccessorGround
    (p : ReversalParity) (N : ℕ) (L : ℝ) : ℝ :=
  parityRayleighBottom p L (N + 1)

/-- Negative values occur arbitrarily close to the right of `Lstar`. -/
def ParityRightCrossesNegative
    (p : ReversalParity) (N : ℕ) (Lstar : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ L : ℝ,
      Lstar < L ∧
      L < Lstar + ε ∧
      paritySuccessorGround p N L < 0

/-- One fixed parity reaches its first negative boundary after a positive
anchor. -/
structure ParityFirstNegativeBoundary where
  p : ReversalParity
  N : ℕ
  one_le_N : 1 ≤ N
  Lsmall : ℝ
  Lstar : ℝ
  Lneg : ℝ
  Lsmall_pos : 0 < Lsmall
  Lsmall_lt_Lstar : Lsmall < Lstar
  Lstar_lt_Lneg : Lstar < Lneg
  base_positive :
    0 < paritySuccessorGround p N Lsmall
  contact_zero :
    paritySuccessorGround p N Lstar = 0
  prefix_nonnegative :
    ∀ L : ℝ, Lsmall ≤ L → L ≤ Lstar →
      0 ≤ paritySuccessorGround p N L
  right_crossing :
    ParityRightCrossesNegative p N Lstar

/-- A global fixed-N positive/negative bracket contains one fixed parity with
the same sign opposition.  This is the parity-selection step used before taking
the first aperture boundary. -/
theorem exists_parity_ground_sign_opposition_of_global
    {N : ℕ}
    {Lsmall Lneg : ℝ}
    (hbase : 1 ≤ globalParitySuccessorBottom Lsmall N)
    (hneg : globalParitySuccessorBottom Lneg N < 0) :
    ∃ p : ReversalParity,
      1 ≤ paritySuccessorGround p N Lsmall ∧
      paritySuccessorGround p N Lneg < 0 := by
  have hevenBase :
      1 ≤ parityRayleighBottom .even Lsmall (N + 1) :=
    le_trans hbase (min_le_left _ _)
  have hoddBase :
      1 ≤ parityRayleighBottom .odd Lsmall (N + 1) :=
    le_trans hbase (min_le_right _ _)
  unfold globalParitySuccessorBottom at hneg
  rw [min_lt_iff] at hneg
  rcases hneg with hevenNeg | hoddNeg
  · exact ⟨.even, by simpa [paritySuccessorGround] using hevenBase,
      by simpa [paritySuccessorGround] using hevenNeg⟩
  · exact ⟨.odd, by simpa [paritySuccessorGround] using hoddBase,
      by simpa [paritySuccessorGround] using hoddNeg⟩

/-- A positive/negative bracket for one fixed parity produces its genuine first
negative boundary.  The boundary is the infimum of the closure of the negative
set on the compact bracket, so the outgoing negative approach is part of the
proved object rather than an extra assumption. -/
theorem exists_parityFirstNegativeBoundary_of_signOpposition
    (p : ReversalParity)
    {N : ℕ} (hN : 1 ≤ N)
    {Lsmall Lneg : ℝ}
    (hLsmall : 0 < Lsmall)
    (hLt : Lsmall < Lneg)
    (hbase : 0 < paritySuccessorGround p N Lsmall)
    (hneg : paritySuccessorGround p N Lneg < 0) :
    ∃ c : ParityFirstNegativeBoundary,
      c.p = p ∧ c.N = N ∧
      c.Lsmall = Lsmall ∧ c.Lneg = Lneg := by
  let g : ℝ → ℝ := fun L => paritySuccessorGround p N L
  let S : Set ℝ :=
    {L | L ∈ Icc Lsmall Lneg ∧ g L < 0}
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
  have hstarpos : 0 < Lstar :=
    lt_of_lt_of_le hLsmall hstarIcc.1
  have hcontAt : ContinuousAt g Lstar := by
    have hwithin :=
      (continuousOn_parityRayleighBottom_succ_Ioi p N hN)
        Lstar hstarpos
    exact hwithin.continuousAt (isOpen_Ioi.mem_nhds hstarpos)

  have hstar_nonpos : g Lstar ≤ 0 := by
    by_contra hnot
    have hpos : 0 < g Lstar := lt_of_not_ge hnot
    have hpre :
        g ⁻¹' Ioi (0 : ℝ) ∈ 𝓝 Lstar :=
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
    have hpre :
        g ⁻¹' Iio (0 : ℝ) ∈ 𝓝 Lstar :=
      hcontAt.tendsto (isOpen_Iio.mem_nhds hnegstar)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
    let η : ℝ := min δ (Lstar - Lsmall)
    have hη : 0 < η := by
      exact lt_min hδ (sub_pos.mpr hsmallstar)
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
    have hstar_le_x : Lstar ≤ x :=
      hleast.2 (subset_closure hxS)
    linarith

  have hcontact : g Lstar = 0 := by
    linarith
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
    have hstar_le_L : Lstar ≤ L :=
      hleast.2 (subset_closure hLS)
    have hEq : L = Lstar := le_antisymm hLLstar hstar_le_L
    subst L
    linarith

  have hright : ParityRightCrossesNegative p N Lstar := by
    intro ε hε
    have hmeet :=
      (mem_closure_iff.mp hstarC)
        (Metric.ball Lstar ε) Metric.isOpen_ball
        (Metric.mem_ball_self hε)
    obtain ⟨L, hLball, hLS⟩ := hmeet
    have hLneg : g L < 0 := by
      change L ∈ Icc Lsmall Lneg ∧ g L < 0 at hLS
      exact hLS.2
    have hstar_le_L : Lstar ≤ L :=
      hleast.2 (subset_closure hLS)
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
    refine ⟨L, hstar_lt_L, hLupper, ?_⟩
    simpa [g, paritySuccessorGround] using hLneg

  let c : ParityFirstNegativeBoundary := {
    p := p
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
  exact ⟨c, rfl, rfl, rfl, rfl⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_parityFirstNegativeBoundary_of_signOpposition
