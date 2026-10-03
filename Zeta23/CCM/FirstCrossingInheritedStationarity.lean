import Zeta23.CCM.FirstCrossingGlobalAlignment
import Zeta23.CCM.CanonicalCompressedApertureC2

noncomputable section

namespace Zeta23.CCM

open Complex Set

/-!
# Post-#282 inherited-contact stationarity

An inherited contact (n < k) carries a predecessor zero direction that is
nonnegative on both sides of the contact.  Its first aperture variation
therefore vanishes.  The result below is intentionally weaker than E' z = 0:
only the restriction of the quadratic derivative to the inherited kernel
vanishes; cross-coupling into the new shell is retained.
-/

/-- Energy of the inherited seed transported to the selected successor. -/
def inheritedSelectedEnergy
    (g : GeneratedGlobalFirstCrossing) (L : ℝ) : ℝ :=
  let z :=
    parityPlateauExtend g.shell.p g.shell.n_le_k
      g.shell.seed
  Complex.re
    (inner ℂ
      (parityCompressedCanonical g.shell.p L (g.shell.k + 1) z) z)

/-- In the inherited case the transported seed is stationary at the generated
contact. -/
theorem GeneratedGlobalFirstCrossing.inheritedSeed_firstVariation_zero
    (g : GeneratedGlobalFirstCrossing)
    (hinh : g.shell.n < g.shell.k) :
    deriv (inheritedSelectedEnergy g) g.shell.Lstar = 0 := by
  let z :=
    parityPlateauExtend g.shell.p g.shell.n_le_k
      g.shell.seed
  have hzker :
      parityCompressedCanonical g.shell.p g.shell.Lstar
          (g.shell.k + 1) z = 0 := by
    exact g.shell.extended_kernel g.shell.k
      g.shell.n_le_k g.shell.k_le_N
  have hleft :
      ∀ L, g.shell.Lsmall ≤ L → L ≤ g.shell.Lstar →
        0 ≤ inheritedSelectedEnergy g L := by
    intro L hLs hLstar
    have hbottom :=
      g.selectedParity_prefix_nonnegative g.shell.p hLs hLstar
    have hq :=
      shiftedParityCompressed_nonnegative_of_le_bottom
        g.shell.p L (g.shell.k + 1) (lam := 0) hbottom z
    simpa [inheritedSelectedEnergy, z] using hq
  have hstable := g.shell.predecessorGround_stable
  have hright :
      ∃ δ > 0, ∀ L, g.shell.Lstar ≤ L → L < g.shell.Lstar + δ →
        0 ≤ inheritedSelectedEnergy g L := by
    rcases hstable with hk1 | ⟨δ,hδ,hpred⟩
    · have : g.shell.k = 1 := hk1
      omega
    · refine ⟨δ,hδ,?_⟩
      intro L hLo hHi
      have hpred0 := hpred L hLo hHi
      have htransport :=
        re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
          (lt_of_lt_of_le g.shell.Lsmall_pos
            (g.shell.prefix_nonnegative _ (le_refl _) (le_of_lt g.shell.Lsmall_lt_Lstar)))
          (Nat.le_succ (g.shell.k - 1))
          (g.shell.seed : EuclideanSpace ℂ
            (Fin (2 * (g.shell.n + 1) + 1)))
      simpa [inheritedSelectedEnergy, z] using hpred0
  have hC2 :=
    canonicalParityCompressedC2_proved g.shell.p (g.shell.k + 1)
  have hdiff :
      HasDerivAt (inheritedSelectedEnergy g)
        (deriv (inheritedSelectedEnergy g) g.shell.Lstar)
        g.shell.Lstar :=
    (hC2 g.shell.Lstar
      (lt_trans g.shell.Lsmall_pos g.shell.Lsmall_lt_Lstar)).differentiableAt.hasDerivAt
  have hzero : inheritedSelectedEnergy g g.shell.Lstar = 0 := by
    simp [inheritedSelectedEnergy, z, hzker]
  have hmin :
      IsLocalMin (inheritedSelectedEnergy g) g.shell.Lstar := by
    rcases hright with ⟨δ,hδ,hright⟩
    refine ⟨Ioo (max g.shell.Lsmall (g.shell.Lstar - δ))
      (g.shell.Lstar + δ), ?_, ?_⟩
    · exact Ioo_mem_nhds (by simp; linarith) (by linarith)
    · intro L hL
      rw [hzero]
      by_cases h : L ≤ g.shell.Lstar
      · exact hleft L (by simpa using hL.1) h
      · exact hright L (le_of_not_ge h) (by simpa using hL.2)
  exact (hmin.deriv_eq_zero hdiff.differentiableAt)

end Zeta23.CCM

#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.inheritedSeed_firstVariation_zero
