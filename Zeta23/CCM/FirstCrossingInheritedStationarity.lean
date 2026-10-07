import Zeta23.CCM.FirstCrossingGlobalAlignment
import Zeta23.CCM.FirstCrossingSchurReduction
import Zeta23.CCM.FirstCrossingProductionFirstVariation
import Zeta23.CCM.CanonicalCompressedApertureC2
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

namespace Zeta23.CCM

open Complex Set Filter
open scoped Topology

/-!
# Post-#282 inherited-contact stationarity

An inherited contact (n < k) carries a predecessor zero direction that is
nonnegative on both sides of the contact.  Its first aperture variation
therefore vanishes.  The result below is intentionally weaker than E' z = 0:
only the restriction of the quadratic derivative to the inherited kernel
vanishes; cross-coupling into the new shell is retained.
-/


/-- Selected-contact zero modes lying in the embedded one-step predecessor. -/
def inheritedContactKernelSubspace
    (g : GeneratedGlobalFirstCrossing) :
    Submodule ℂ
      (euclideanParityBoundaryFlatSubspace g.shell.p (g.shell.k + 1)) :=
  intrinsicParityPredecessorSubspace g.shell.p g.shell.k ⊓
    LinearMap.ker
      (parityCompressedCanonical g.shell.p g.shell.Lstar
        (g.shell.k + 1))

/-- Fixed-vector energy on the inherited contact-kernel subspace. -/
def inheritedContactKernelEnergy
    (g : GeneratedGlobalFirstCrossing)
    (x : inheritedContactKernelSubspace g)
    (L : ℝ) : ℝ :=
  productionContactFixedEnergy g.shell.p L (g.shell.k + 1)
    (x : euclideanParityBoundaryFlatSubspace g.shell.p (g.shell.k + 1))

/-- Inherited contact-kernel vectors remain nonnegative on a right
neighborhood because the predecessor ground is stable there. -/
theorem GeneratedGlobalFirstCrossing.inheritedContactKernel_right_nonnegative
    (g : GeneratedGlobalFirstCrossing)
    (hinh : g.shell.n < g.shell.k)
    (x : inheritedContactKernelSubspace g) :
    ∃ δ > 0, ∀ L,
      g.shell.Lstar ≤ L → L < g.shell.Lstar + δ →
        0 ≤ inheritedContactKernelEnergy g x L := by
  have hxpred :
      ((x :
        euclideanParityBoundaryFlatSubspace g.shell.p (g.shell.k + 1)) :
          EuclideanSpace ℂ (Fin (2 * (g.shell.k + 1) + 1))) ∈
        euclideanParityEmbeddedSuccSubspace g.shell.p g.shell.k :=
    x.property.1
  rcases hxpred with ⟨y, hy, hxy⟩
  rcases g.shell.predecessorGround_stable with hk1 | ⟨δ,hδ,hstable⟩
  · have hn1 : 1 ≤ g.shell.n := g.shell.one_le_n
    omega
  · refine ⟨δ,hδ,?_⟩
    intro L hLo hHi
    have hbottomSucc := hstable L hLo hHi
    have hsucc : g.shell.k - 1 + 1 = g.shell.k := by omega
    have hbottom :
        0 ≤ parityRayleighBottom g.shell.p L g.shell.k := by
      simpa [paritySuccessorGround, hsucc] using hbottomSucc
    have hprev :
        PredecessorSectorNonnegative g.shell.p L g.shell.k :=
      predecessorSectorNonnegative_of_parityBottom_nonnegative
        g.shell.p L g.shell.k hbottom
    have hLpos : 0 < L :=
      lt_of_lt_of_le
        (lt_trans g.shell.Lsmall_pos g.shell.Lsmall_lt_Lstar) hLo
    have hsuccEnergy :=
      re_inner_successor_nonnegative_on_centeredImage
        g.shell.p hLpos g.shell.k hprev y hy
    change
      euclideanCenteredZeroExtend (Nat.le_succ g.shell.k) y =
        ((x :
          euclideanParityBoundaryFlatSubspace g.shell.p
            (g.shell.k + 1)) :
          EuclideanSpace ℂ (Fin (2 * (g.shell.k + 1) + 1))) at hxy
    rw [hxy] at hsuccEnergy
    unfold inheritedContactKernelEnergy productionContactFixedEnergy
    rw [re_inner_parityCompressedCanonical_self]
    exact hsuccEnergy

/-- Left-prefix nonnegativity plus exact zero energy at contact. -/
theorem GeneratedGlobalFirstCrossing.inheritedContactKernel_left_and_contact
    (g : GeneratedGlobalFirstCrossing)
    (x : inheritedContactKernelSubspace g) :
    (∀ L, g.shell.Lsmall ≤ L → L ≤ g.shell.Lstar →
      0 ≤ inheritedContactKernelEnergy g x L) ∧
      inheritedContactKernelEnergy g x g.shell.Lstar = 0 := by
  constructor
  · intro L hsmall hstar
    have hbottom :=
      g.selectedParity_prefix_nonnegative g.shell.p hsmall hstar
    have hq :=
      parityRayleighBottom_mul_norm_sq_le
        g.shell.p L (g.shell.k + 1)
        (x : euclideanParityBoundaryFlatSubspace
          g.shell.p (g.shell.k + 1))
    have hmul :
        0 ≤ parityRayleighBottom g.shell.p L (g.shell.k + 1) *
          ‖(x : euclideanParityBoundaryFlatSubspace
            g.shell.p (g.shell.k + 1))‖ ^ 2 :=
      mul_nonneg hbottom (sq_nonneg _)
    unfold inheritedContactKernelEnergy productionContactFixedEnergy
    exact le_trans hmul hq
  · have hxker :
        parityCompressedCanonical g.shell.p g.shell.Lstar
          (g.shell.k + 1)
          (x : euclideanParityBoundaryFlatSubspace
            g.shell.p (g.shell.k + 1)) = 0 :=
      LinearMap.mem_ker.mp x.property.2
    simp [inheritedContactKernelEnergy, productionContactFixedEnergy, hxker]

/-- F06 quadratic statement: the actual compressed first aperture jet has
zero real quadratic form on the inherited predecessor-kernel subspace. -/
theorem GeneratedGlobalFirstCrossing.inheritedContactKernel_firstJet_re_zero
    (g : GeneratedGlobalFirstCrossing)
    (hinh : g.shell.n < g.shell.k)
    (x : inheritedContactKernelSubspace g) :
    Complex.re
      (inner ℂ
        (canonicalParityApertureFirst g.shell.p g.shell.Lstar
          (g.shell.k + 1)
          (x : euclideanParityBoundaryFlatSubspace
            g.shell.p (g.shell.k + 1)))
        (x : euclideanParityBoundaryFlatSubspace
          g.shell.p (g.shell.k + 1))) = 0 := by
  obtain ⟨hleft,hzero⟩ :=
    g.inheritedContactKernel_left_and_contact x
  obtain ⟨δ,hδ,hright⟩ :=
    g.inheritedContactKernel_right_nonnegative hinh x
  have hIoo :
      Ioo
        (max g.shell.Lsmall (g.shell.Lstar - δ))
        (g.shell.Lstar + δ) ∈ 𝓝 g.shell.Lstar := by
    apply Ioo_mem_nhds
    · exact
        max_lt g.shell.Lsmall_lt_Lstar
          (sub_lt_self _ hδ)
    · linarith
  have hmin :
      IsLocalMin (inheritedContactKernelEnergy g x) g.shell.Lstar := by
    filter_upwards [hIoo] with L hL
    change inheritedContactKernelEnergy g x g.shell.Lstar ≤
      inheritedContactKernelEnergy g x L
    rw [hzero]
    by_cases h : L ≤ g.shell.Lstar
    · have hsmall : g.shell.Lsmall ≤ L :=
        le_trans (le_max_left _ _) (le_of_lt hL.1)
      exact hleft L hsmall h
    · exact hright L (le_of_lt (lt_of_not_ge h)) hL.2
  have hderiv :
      HasDerivAt (inheritedContactKernelEnergy g x)
        (Complex.re
          (inner ℂ
            (canonicalParityApertureFirst g.shell.p g.shell.Lstar
              (g.shell.k + 1)
              (x : euclideanParityBoundaryFlatSubspace
                g.shell.p (g.shell.k + 1)))
            (x : euclideanParityBoundaryFlatSubspace
              g.shell.p (g.shell.k + 1))))
        g.shell.Lstar := by
    change
      HasDerivAt
        (fun s : ℝ =>
          productionContactFixedEnergy g.shell.p s (g.shell.k + 1)
            (x : euclideanParityBoundaryFlatSubspace
              g.shell.p (g.shell.k + 1)))
        (Complex.re
          (inner ℂ
            (canonicalParityApertureFirst g.shell.p g.shell.Lstar
              (g.shell.k + 1)
              (x : euclideanParityBoundaryFlatSubspace
                g.shell.p (g.shell.k + 1)))
            (x : euclideanParityBoundaryFlatSubspace
              g.shell.p (g.shell.k + 1))))
        g.shell.Lstar
    exact
      canonicalParity_fixedEnergy_hasDerivAt
        g.shell.p
        (lt_trans g.shell.Lsmall_pos g.shell.Lsmall_lt_Lstar)
        (g.shell.k + 1)
        (x : euclideanParityBoundaryFlatSubspace
          g.shell.p (g.shell.k + 1))
  exact hmin.hasDerivAt_eq_zero hderiv

/-- The complex quadratic form vanishes as well; symmetry supplies its
imaginary part. -/
theorem GeneratedGlobalFirstCrossing.inheritedContactKernel_firstJet_inner_zero
    (g : GeneratedGlobalFirstCrossing)
    (hinh : g.shell.n < g.shell.k)
    (x : inheritedContactKernelSubspace g) :
    inner ℂ
      (canonicalParityApertureFirst g.shell.p g.shell.Lstar
        (g.shell.k + 1)
        (x : euclideanParityBoundaryFlatSubspace
          g.shell.p (g.shell.k + 1)))
      (x : euclideanParityBoundaryFlatSubspace
        g.shell.p (g.shell.k + 1)) = 0 := by
  have hre :=
    g.inheritedContactKernel_firstJet_re_zero hinh x
  have hsym :=
    canonicalParityApertureFirst_isSymmetric g.shell.p
      (lt_trans g.shell.Lsmall_pos g.shell.Lsmall_lt_Lstar)
      (g.shell.k + 1)
  have him :
      (inner ℂ
        (canonicalParityApertureFirst g.shell.p g.shell.Lstar
          (g.shell.k + 1)
          (x : euclideanParityBoundaryFlatSubspace
            g.shell.p (g.shell.k + 1)))
        (x : euclideanParityBoundaryFlatSubspace
          g.shell.p (g.shell.k + 1))).im = 0 := by
    simpa using hsym.im_inner_apply_self
      (x : euclideanParityBoundaryFlatSubspace
        g.shell.p (g.shell.k + 1))
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- Exact projected restriction of the first aperture jet to the inherited
contact kernel. -/
noncomputable def inheritedContactFirstJetRestriction
    (g : GeneratedGlobalFirstCrossing) :
    inheritedContactKernelSubspace g →ₗ[ℂ]
      inheritedContactKernelSubspace g := by
  let V :=
    euclideanParityBoundaryFlatSubspace g.shell.p (g.shell.k + 1)
  let K : Submodule ℂ V :=
    inheritedContactKernelSubspace g
  let Pclm : V →L[ℂ] K :=
    Submodule.orthogonalProjectionOnto
      (𝕜 := ℂ) (E := V) K
  let P : V →ₗ[ℂ] K :=
    Pclm.toLinearMap
  let E₁ : V →ₗ[ℂ] V :=
    canonicalParityApertureFirst
      g.shell.p g.shell.Lstar (g.shell.k + 1)
  exact P.comp (E₁.comp K.subtype)

/-- Polarization conclusion: the projected restriction of the first jet is
zero. Cross-coupling out of the inherited kernel is deliberately not claimed. -/
theorem GeneratedGlobalFirstCrossing.inheritedContactFirstJetRestriction_eq_zero
    (g : GeneratedGlobalFirstCrossing)
    (hinh : g.shell.n < g.shell.k) :
    inheritedContactFirstJetRestriction g = 0 := by
  refine
    (inner_map_self_eq_zero
      (V := inheritedContactKernelSubspace g)
      (inheritedContactFirstJetRestriction g)).mp ?_
  intro x
  change
    inner ℂ
      ((inheritedContactKernelSubspace g).orthogonalProjectionOnto
        (canonicalParityApertureFirst g.shell.p g.shell.Lstar
          (g.shell.k + 1)
          (x : euclideanParityBoundaryFlatSubspace
            g.shell.p (g.shell.k + 1))))
      x = 0
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact g.inheritedContactKernel_firstJet_inner_zero hinh x

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
  have hrightGround :
      ∃ δ > 0, ∀ L,
        g.shell.Lstar ≤ L → L < g.shell.Lstar + δ →
          0 ≤ paritySuccessorGround g.shell.p g.shell.n L := by
    have hnot :
        ¬ ParityRightCrossesNegative
          g.shell.p g.shell.n g.shell.Lstar :=
      g.shell.earlier_plateau_no_right_crossing
        g.shell.n le_rfl hinh
    by_contra hstable
    push_neg at hstable
    apply hnot
    intro ε hε
    obtain ⟨L,hLo,hHi,hNeg⟩ := hstable ε hε
    have hstrict : g.shell.Lstar < L := by
      rcases lt_or_eq_of_le hLo with h | h
      · exact h
      · subst L
        have hnN : g.shell.n ≤ g.shell.N :=
          le_trans g.shell.n_le_k g.shell.k_le_N
        have hnzero :
            paritySuccessorGround g.shell.p g.shell.n
              g.shell.Lstar = 0 :=
          g.shell.plateau_zero g.shell.n le_rfl hnN
        rw [hnzero] at hNeg
        linarith
    exact ⟨L,hstrict,hHi,hNeg⟩
  obtain ⟨δ,hδ,hrightGround⟩ := hrightGround
  have hright :
      ∀ L, g.shell.Lstar ≤ L → L < g.shell.Lstar + δ →
        0 ≤ inheritedSelectedEnergy g L := by
    intro L hLo hHi
    have hLpos : 0 < L :=
      lt_of_lt_of_le
        (lt_trans g.shell.Lsmall_pos g.shell.Lsmall_lt_Lstar) hLo
    have hbottom :
        0 ≤ parityRayleighBottom g.shell.p L (g.shell.n + 1) := by
      simpa [paritySuccessorGround] using hrightGround L hLo hHi
    have hq :=
      parityRayleighBottom_mul_norm_sq_le
        g.shell.p L (g.shell.n + 1) g.shell.seed
    have hseed :
        0 ≤ Complex.re
          (inner ℂ
            (parityCompressedCanonical g.shell.p L
              (g.shell.n + 1) g.shell.seed)
            g.shell.seed) :=
      le_trans
        (mul_nonneg hbottom (sq_nonneg ‖g.shell.seed‖))
        hq
    rw [re_inner_parityCompressedCanonical_self] at hseed
    have htransport :=
      re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
        hLpos (Nat.succ_le_succ g.shell.n_le_k)
        (g.shell.seed : EuclideanSpace ℂ
          (Fin (2 * (g.shell.n + 1) + 1)))
    rw [← htransport] at hseed
    change
      0 ≤ Complex.re
        (inner ℂ
          (parityCompressedCanonical g.shell.p L
            (g.shell.k + 1) z)
          z)
    rw [re_inner_parityCompressedCanonical_self]
    simpa [z, parityPlateauExtend] using hseed
  have hzero : inheritedSelectedEnergy g g.shell.Lstar = 0 := by
    simp [inheritedSelectedEnergy, z, hzker]
  have hIoo :
      Ioo
        (max g.shell.Lsmall (g.shell.Lstar - δ))
        (g.shell.Lstar + δ) ∈ 𝓝 g.shell.Lstar := by
    apply Ioo_mem_nhds
    · exact
        max_lt g.shell.Lsmall_lt_Lstar
          (sub_lt_self _ hδ)
    · linarith
  have hmin :
      IsLocalMin (inheritedSelectedEnergy g) g.shell.Lstar := by
    filter_upwards [hIoo] with L hL
    rw [hzero]
    by_cases h : L ≤ g.shell.Lstar
    · have hsmall : g.shell.Lsmall ≤ L :=
        le_trans (le_max_left _ _) (le_of_lt hL.1)
      exact hleft L hsmall h
    · exact hright L (le_of_lt (lt_of_not_ge h)) hL.2
  exact hmin.deriv_eq_zero

end Zeta23.CCM

#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.inheritedContactFirstJetRestriction_eq_zero
#print axioms Zeta23.CCM.GeneratedGlobalFirstCrossing.inheritedSeed_firstVariation_zero
