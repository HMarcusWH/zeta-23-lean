import Zeta23.OPICARound4.RegularCells.NativeParityNonidentity
import Zeta23.OPICARound4.RegularCells.NativeRegularBirthSelection

noncomputable section
namespace Zeta23.OPICARound4.NativeParityPencils
open CCM RegularCells ExceptionalZero OPICARound3 Filter Set
open scoped Topology

theorem isOpen_positive_nativeActualSeparationDet_nonzero (Q K : ℕ) :
    IsOpen {L : ℝ | 0 < L ∧ nativeActualSeparationDet Q K (L : ℂ) ≠ 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro L hL
  have hfT : Tendsto (nativeActualSeparationDet Q K) (𝓝 (L : ℂ))
      (𝓝 (nativeActualSeparationDet Q K (L : ℂ))) :=
    (analyticOnNhd_nativeActualSeparationDet Q K (L : ℂ)
      ((ofReal_mem_complexFrozenSourceDomain_iff L).mpr hL.1.ne')).continuousAt
  have hT := hfT.comp (Complex.continuous_ofReal.tendsto L)
  have hn : ({0}ᶜ : Set ℂ) ∈ 𝓝 (nativeActualSeparationDet Q K (L : ℂ)) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hL.2)
  filter_upwards [isOpen_Ioi.mem_nhds hL.1,hT hn] with r hr hnr
  exact ⟨hr,by simpa using hnr⟩

/-- The complete two finite families are prescribed before the aperture is chosen. -/
theorem exists_regular_and_separationDet_in_open_fixedCell {Q : ℕ} (hQ : 2 ≤ Q)
    (s : Finset ℕ) (hs : ∀ K ∈ s, 3 ≤ K) (t : Finset (ReversalParity × ℕ))
    {J : Set ℝ} (hJo : IsOpen J) (hJn : J.Nonempty)
    (hJc : J ⊆ fixedCanonicalCutoffCell Q) :
    ∃ L ∈ J, (∀ i ∈ t, Function.Bijective (nativePoleNeutralParityCanonical i.1 L i.2)) ∧
      ∀ K ∈ s, nativeActualSeparationDet Q K (L : ℂ) ≠ 0 := by
  classical
  have hQ1 : 1 ≤ Q := by omega
  have hJp : J ⊆ Ioi 0 := fun L hL => fixedCanonicalCutoffCell_subset_Ioi hQ1 (hJc hL)
  obtain ⟨L0,hL0J,hL0s⟩ := exists_finite_nativeActualSeparationDet_nonzero Q hQ s hs hJo hJn hJp
  let U : Set ℝ := J ∩ ⋂ K ∈ s, {L : ℝ | 0 < L ∧ nativeActualSeparationDet Q K (L : ℂ) ≠ 0}
  have hUo : IsOpen U := hJo.inter (isOpen_biInter_finset
    (fun K _ => isOpen_positive_nativeActualSeparationDet_nonzero Q K))
  have hL0U : L0 ∈ U := by
    refine ⟨hL0J,?_⟩
    simp only [mem_iInter,mem_ofPred_eq]
    exact fun K hK => ⟨hJp hL0J,hL0s K hK⟩
  obtain ⟨L,hLU,hLreg⟩ := exists_finite_native_regular_in_open_fixedCell hQ1 t hUo
    ⟨L0,hL0U⟩ (fun L hL => hJc hL.1)
  refine ⟨L,hLU.1,hLreg,?_⟩
  intro K hK
  have h := hLU.2
  simp only [mem_iInter,mem_ofPred_eq] at h
  exact (h K hK).2

theorem exists_bounded_regular_and_separationDet_in_open_above_one (N : ℕ)
    {J : Set ℝ} (hJo : IsOpen J) (hJn : J.Nonempty) (hJ1 : J ⊆ Ioi 1) :
    ∃ L ∈ J, (∀ (p : ReversalParity) (K : ℕ), K ≤ N →
      Function.Bijective (nativePoleNeutralParityCanonical p L K)) ∧
      ∀ K : ℕ, 3 ≤ K → K ≤ N → nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0 := by
  classical
  have hJp : J ⊆ Ioi 0 := by
    intro L hL
    have hL1 : 1 < L := hJ1 hL
    change 0 < L
    linarith
  obtain ⟨Q,U,hQ1,hUo,hUn,hUJ,hUc⟩ := exists_open_fixedCell_subset_positive hJo hJn hJp
  obtain ⟨L0,hL0⟩ := hUn
  have hfloor := natFloor_exp_eq_on_fixedCanonicalCutoffCell hQ1 (hUc hL0)
  have hQ : 2 ≤ Q := by
    rw [← hfloor]
    apply (Nat.le_floor_iff (Real.exp_nonneg L0)).mpr
    change (2 : ℝ) ≤ Real.exp L0
    have hL : 1 < L0 := hJ1 (hUJ hL0)
    have he := Real.add_one_le_exp L0
    linarith
  let t := ({ReversalParity.even,ReversalParity.odd} : Finset ReversalParity).product (Finset.range (N+1))
  obtain ⟨L,hLU,hreg,hsep⟩ := exists_regular_and_separationDet_in_open_fixedCell hQ
    (Finset.Icc 3 N) (fun K hK => (Finset.mem_Icc.mp hK).1) t hUo ⟨L0,hL0⟩ hUc
  refine ⟨L,hUJ hLU,?_,?_⟩
  · intro p K hK
    apply hreg (p,K)
    exact Finset.mem_product.mpr ⟨by cases p <;> simp,Finset.mem_range.mpr (by omega)⟩
  · intro K hK hKN
    rw [natFloor_exp_eq_on_fixedCanonicalCutoffCell hQ1 (hUc hLU)]
    exact hsep K (Finset.mem_Icc.mpr ⟨hK,hKN⟩)

/-- Off-line zeros force arbitrarily late common-quartic negative states at which
all bounded native zero determinants and full cross-parity separation determinants
are nonzero. No previously chosen detector's quantitative depth is transferred. -/
theorem cofinally_both_negative_regular_and_separationDet (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1/2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ 2 ≤ L ∧ BothNeutralNegative L (originalDetectorQuarticCutoff L) ∧
      (∀ (p : ReversalParity) (K : ℕ), K ≤ originalDetectorQuarticCutoff L →
        Function.Bijective (nativePoleNeutralParityCanonical p L K)) ∧
      ∀ K : ℕ, 3 ≤ K → K ≤ originalDetectorQuarticCutoff L →
        nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0 := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (eventually_both_negative_at_original_quartic ρ hoff)
  let B := max (max R R0) 2
  let N := Nat.ceil ((B+1)^4)
  have hB : 2 ≤ B := le_max_right _ _
  have hJ1 : Ioo B (B+1) ⊆ Ioi 1 := by intro L hL; change 1 < L; linarith [hL.1]
  obtain ⟨L,hLJ,hreg,hsep⟩ := exists_bounded_regular_and_separationDet_in_open_above_one N
    isOpen_Ioo (Set.nonempty_Ioo.mpr (by linarith)) hJ1
  have hR : R < L := (le_max_left R R0 |>.trans (le_max_left _ _)).trans_lt hLJ.1
  have hR0L : R0 ≤ L := (le_max_right R R0 |>.trans (le_max_left _ _)).trans hLJ.1.le
  obtain ⟨hL2,hboth⟩ := hR0 L hR0L
  have hcap : originalDetectorQuarticCutoff L ≤ N := by
    apply Nat.ceil_mono
    exact pow_le_pow_left₀ (by linarith) hLJ.2.le 4
  exact ⟨L,hR,hL2,hboth,fun p K hK => hreg p K (hK.trans hcap),
    fun K hK hKN => hsep K hK (hKN.trans hcap)⟩

end Zeta23.OPICARound4.NativeParityPencils
