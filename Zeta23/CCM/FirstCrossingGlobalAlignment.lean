import Zeta23.CCM.GlobalParityFirstNegativeBoundary
import Zeta23.CCM.CanonicalParityFirstCrossingShell
import Zeta23.CCM.GlobalParityBottomNFlow

noncomputable section

namespace Zeta23.CCM

open Set
open scoped Topology

/-!
# Post-#281 global/contact alignment

The global first-negative boundary supplies a common aperture and fixed terminal
cutoff.  This module chooses one parity that is genuinely responsible for
arbitrarily-close right-hand negativity, builds the existing parity plateau /
kernel-tower / first-crossing-shell machinery at the same aperture, and then
transports the global nonnegativity information down to the selected cutoff.

No WLOG-even reduction is used.
-/

/-- Some parity is negative arbitrarily close to every global first-negative
boundary. -/
theorem GlobalParityFirstNegativeBoundary.exists_responsibleParity
    (c : GlobalParityFirstNegativeBoundary) :
    ∃ p : ReversalParity,
      ParityRightCrossesNegative p c.N c.Lstar := by
  classical
  by_cases heven : ParityRightCrossesNegative .even c.N c.Lstar
  · exact ⟨.even, heven⟩
  · have hevenStable :
        ∃ δ : ℝ, 0 < δ ∧
          ∀ L : ℝ,
            c.Lstar < L → L < c.Lstar + δ →
              0 ≤ paritySuccessorGround .even c.N L := by
      unfold ParityRightCrossesNegative at heven
      push_neg at heven
      obtain ⟨δ, hδpos, hδ⟩ := heven
      refine ⟨δ, hδpos, ?_⟩
      intro L hLlo hLhi
      exact le_of_not_gt (hδ L hLlo hLhi)
    obtain ⟨δe, hδe, hevenNonneg⟩ := hevenStable
    refine ⟨.odd, ?_⟩
    intro ε hε
    let η : ℝ := min ε δe
    have hη : 0 < η := lt_min hε hδe
    obtain ⟨L, hLlo, hLhi, hglobalNeg⟩ := c.right_crossing η hη
    have hηe : η ≤ δe := min_le_right _ _
    have hηeps : η ≤ ε := min_le_left _ _
    have hevenL : 0 ≤ paritySuccessorGround .even c.N L :=
      hevenNonneg L hLlo (by linarith)
    have hoddL : paritySuccessorGround .odd c.N L < 0 := by
      unfold globalParitySuccessorBottom at hglobalNeg
      rw [min_lt_iff] at hglobalNeg
      rcases hglobalNeg with h | h
      · linarith
      · exact h
    exact ⟨L, hLlo, by linarith, hoddL⟩

/-- A responsible parity is exactly zero at the global boundary. -/
theorem GlobalParityFirstNegativeBoundary.responsibleParity_contact_zero
    (c : GlobalParityFirstNegativeBoundary)
    (p : ReversalParity)
    (hright : ParityRightCrossesNegative p c.N c.Lstar) :
    paritySuccessorGround p c.N c.Lstar = 0 := by
  have hnonneg : 0 ≤ paritySuccessorGround p c.N c.Lstar := by
    have hglobal : 0 ≤ globalParitySuccessorBottom c.Lstar c.N := by
      rw [c.contact_zero]
    unfold globalParitySuccessorBottom at hglobal
    cases p with
    | even => exact le_trans hglobal (min_le_left _ _)
    | odd => exact le_trans hglobal (min_le_right _ _)
  by_contra hne
  have hpos : 0 < paritySuccessorGround p c.N c.Lstar :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hstarpos : 0 < c.Lstar := lt_trans c.Lsmall_pos c.Lsmall_lt_Lstar
  have hcontWithin :=
    (continuousOn_parityRayleighBottom_succ_Ioi p c.N c.one_le_N)
      c.Lstar hstarpos
  have hcont := hcontWithin.continuousAt (isOpen_Ioi.mem_nhds hstarpos)
  have hpre :
      (fun L : ℝ => paritySuccessorGround p c.N L) ⁻¹' Ioi (0 : ℝ) ∈
        𝓝 c.Lstar := by
    exact hcont.tendsto (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨L, hLlo, _hLhi, hLneg⟩ := hright δ hδ
  have hdist : dist L c.Lstar < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt hLlo))]
    linarith
  have hLpos : 0 < paritySuccessorGround p c.N L :=
    hball (by simpa only [Metric.mem_ball] using hdist)
  linarith

/-- Build the existing one-parity first-negative-boundary package without
changing the global contact aperture. -/
theorem GlobalParityFirstNegativeBoundary.exists_alignedParityBoundary
    (c : GlobalParityFirstNegativeBoundary) :
    ∃ b : ParityFirstNegativeBoundary,
      b.N = c.N ∧
      b.Lsmall = c.Lsmall ∧
      b.Lstar = c.Lstar ∧
      b.Lneg = c.Lneg := by
  obtain ⟨p, hright⟩ := c.exists_responsibleParity
  have hbase : 0 < paritySuccessorGround p c.N c.Lsmall := by
    have hglobal := c.base_positive
    unfold globalParitySuccessorBottom at hglobal
    cases p with
    | even => exact lt_of_lt_of_le hglobal (min_le_left _ _)
    | odd => exact lt_of_lt_of_le hglobal (min_le_right _ _)
  let b : ParityFirstNegativeBoundary := {
    p := p
    N := c.N
    one_le_N := c.one_le_N
    Lsmall := c.Lsmall
    Lstar := c.Lstar
    Lneg := c.Lneg
    Lsmall_pos := c.Lsmall_pos
    Lsmall_lt_Lstar := c.Lsmall_lt_Lstar
    Lstar_lt_Lneg := c.Lstar_lt_Lneg
    base_positive := hbase
    contact_zero := c.responsibleParity_contact_zero p hright
    prefix_nonnegative := by
      intro L h1 h2
      exact c.prefix_eachParity_nonnegative p h1 h2
    right_crossing := hright
  }
  exact ⟨b, rfl, rfl, rfl, rfl⟩

/-- Global first-negative-boundary data aligned to the exact selected parity
shell. -/
structure GeneratedGlobalFirstCrossing where
  global : GlobalParityFirstNegativeBoundary
  shell : CanonicalParityFirstCrossingShell
  same_N : shell.N = global.N
  same_Lsmall : shell.Lsmall = global.Lsmall
  same_Lstar : shell.Lstar = global.Lstar
  same_Lneg : shell.Lneg = global.Lneg

/-- Every global boundary produces an aligned selected parity shell. -/
theorem GlobalParityFirstNegativeBoundary.exists_generatedGlobalFirstCrossing
    (c : GlobalParityFirstNegativeBoundary) :
    ∃ g : GeneratedGlobalFirstCrossing,
      g.global = c := by
  obtain ⟨b, hbN, hbsmall, hbstar, hbneg⟩ :=
    c.exists_alignedParityBoundary
  obtain ⟨z, hz⟩ := b.exists_zeroPlateau
  obtain ⟨t, ht⟩ := z.exists_kernelTower
  obtain ⟨s, hs⟩ := t.exists_firstCrossingShell
  have hsN : s.N = c.N := by
    rw [← hbN]
    simpa [hs, ht, hz]
  have hssmall : s.Lsmall = c.Lsmall := by
    rw [← hbsmall]
    simpa [hs, ht, hz]
  have hsstar : s.Lstar = c.Lstar := by
    rw [← hbstar]
    simpa [hs, ht, hz]
  have hsneg : s.Lneg = c.Lneg := by
    rw [← hbneg]
    simpa [hs, ht, hz]
  let g : GeneratedGlobalFirstCrossing := {
    global := c
    shell := s
    same_N := hsN
    same_Lsmall := hssmall
    same_Lstar := hsstar
    same_Lneg := hsneg
  }
  exact ⟨g, rfl⟩

/-- The terminal global nonnegativity descends to either parity at the selected
smaller cutoff. -/
theorem GeneratedGlobalFirstCrossing.selectedParity_nonnegative
    (g : GeneratedGlobalFirstCrossing)
    (p : ReversalParity) :
    0 ≤ parityRayleighBottom p g.shell.Lstar (g.shell.k + 1) := by
  have hstarpos : 0 < g.global.Lstar :=
    lt_trans g.global.Lsmall_pos g.global.Lsmall_lt_Lstar
  have hterminal :
      0 ≤ parityRayleighBottom p g.global.Lstar (g.global.N + 1) := by
    have h :=
      g.global.prefix_eachParity_nonnegative p
        (le_of_lt g.global.Lsmall_lt_Lstar) le_rfl
    simpa [paritySuccessorGround] using h
  have hkN : g.shell.k ≤ g.global.N := by
    rw [← g.same_N]
    exact g.shell.k_le_N
  have hk1 : 1 ≤ g.shell.k := le_trans g.shell.one_le_n g.shell.n_le_k
  have hanti :=
    parityRayleighBottom_succ_antitone_of_le
      p hstarpos hk1 hkN
  rw [← g.same_Lstar] at hterminal hanti
  linarith

/-- At the selected cutoff the global bottom is exactly zero, not merely the
selected-parity bottom. -/
theorem GeneratedGlobalFirstCrossing.selected_global_bottom_zero
    (g : GeneratedGlobalFirstCrossing) :
    globalParitySuccessorBottom g.shell.Lstar g.shell.k = 0 := by
  have hsel :
      parityRayleighBottom g.shell.p g.shell.Lstar (g.shell.k + 1) = 0 := by
    simpa [paritySuccessorGround] using
      g.shell.plateau_zero g.shell.k g.shell.n_le_k g.shell.k_le_N
  have he := g.selectedParity_nonnegative .even
  have ho := g.selectedParity_nonnegative .odd
  unfold globalParitySuccessorBottom
  cases hp : g.shell.p with
  | even =>
      change parityRayleighBottom .even g.shell.Lstar (g.shell.k + 1) = 0 at hsel
      rw [hsel]
      simp [ho]
  | odd =>
      change parityRayleighBottom .odd g.shell.Lstar (g.shell.k + 1) = 0 at hsel
      rw [hsel]
      simp [he]

/-- Exact parity trichotomy at the selected cutoff. -/
theorem GeneratedGlobalFirstCrossing.selectedParityBranch
    (g : GeneratedGlobalFirstCrossing) :
    ZeroContactParityBranch g.shell.Lstar g.shell.k :=
  zeroContactParityBranch_of_globalParitySuccessorBottom_eq_zero
    g.selected_global_bottom_zero

end Zeta23.CCM

#print axioms Zeta23.CCM.GlobalParityFirstNegativeBoundary.exists_responsibleParity
#print axioms Zeta23.CCM.GlobalParityFirstNegativeBoundary.exists_generatedGlobalFirstCrossing
#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.selected_global_bottom_zero
#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.selectedParityBranch
