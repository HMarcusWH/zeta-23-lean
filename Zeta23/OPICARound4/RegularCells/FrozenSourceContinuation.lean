import Zeta23.CCM.CanonicalApertureSourceHolomorphy
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
namespace Zeta23.OPICARound4.RegularCells
open CCM Complex Set Filter
open scoped Topology

/-- Removing the origin from the actual safe strip leaves one connected
analytic domain, including both halves of the real aperture line. -/
theorem isPreconnected_complexFrozenSourceDomain :
    IsPreconnected complexFrozenSourceDomain := by
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  let U := complexArchSafeStrip ∩ {z : ℂ | 0 < z.im}
  let R := complexArchSafeStrip ∩ {z : ℂ | 0 < z.re}
  let D := complexArchSafeStrip ∩ {z : ℂ | z.im < 0}
  let L := complexArchSafeStrip ∩ {z : ℂ | z.re < 0}
  have hU : IsPreconnected U :=
    (convex_complexArchSafeStrip.inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hR : IsPreconnected R :=
    (convex_complexArchSafeStrip.inter (convex_halfSpace_re_gt 0)).isPreconnected
  have hD : IsPreconnected D :=
    (convex_complexArchSafeStrip.inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hL : IsPreconnected L :=
    (convex_complexArchSafeStrip.inter (convex_halfSpace_re_lt 0)).isPreconnected
  have hUR : (U ∩ R).Nonempty := by
    refine ⟨1 + Complex.I, ?_⟩
    simp [U,R,complexArchSafeStrip,hpi]
  have hDL : (D ∩ L).Nonempty := by
    refine ⟨-1 - Complex.I, ?_⟩
    simp [D,L,complexArchSafeStrip,hpi]
  have hmid : ((U ∪ R) ∩ (D ∪ L)).Nonempty := by
    refine ⟨1 - Complex.I, ?_⟩
    simp [U,R,D,L,complexArchSafeStrip,hpi]
  have heq : complexFrozenSourceDomain = (U ∪ R) ∪ (D ∪ L) := by
    ext z
    simp only [complexFrozenSourceDomain,U,R,D,L,Set.mem_sdiff,mem_singleton_iff,
      mem_union,mem_inter_iff,mem_setOf_eq]
    constructor
    · rintro ⟨hs,hz⟩
      have hparts : z.re ≠ 0 ∨ z.im ≠ 0 := by
        by_contra hn
        push_neg at hn
        exact hz (Complex.ext hn.1 hn.2)
      rcases hparts with hr | hi
      · rcases lt_or_gt_of_ne hr with h | h
        · exact Or.inr (Or.inr ⟨hs,h⟩)
        · exact Or.inl (Or.inr ⟨hs,h⟩)
      · rcases lt_or_gt_of_ne hi with h | h
        · exact Or.inr (Or.inl ⟨hs,h⟩)
        · exact Or.inl (Or.inl ⟨hs,h⟩)
    · rintro ((⟨hs,h⟩ | ⟨hs,h⟩) | (⟨hs,h⟩ | ⟨hs,h⟩)) <;>
        refine ⟨hs,?_⟩ <;> intro hz <;> subst z <;> simpa using h
  rw [heq]
  exact IsPreconnected.union' hmid (IsPreconnected.union' hUR hU hR)
    (IsPreconnected.union' hDL hD hL)

theorem isConnected_complexFrozenSourceDomain :
    IsConnected complexFrozenSourceDomain :=
  ⟨⟨1, by simpa using (ofReal_mem_complexFrozenSourceDomain_iff (1 : ℝ)).mpr one_ne_zero⟩,
    isPreconnected_complexFrozenSourceDomain⟩

theorem eventually_mem_complexFrozenSourceDomain_at_zero :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ complexFrozenSourceDomain := by
  have hs0 : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ complexArchSafeStrip :=
    isOpen_complexArchSafeStrip.mem_nhds zero_mem_complexArchSafeStrip
  have hs : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ complexArchSafeStrip :=
    hs0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hs,self_mem_nhdsWithin] with z hz hn
  exact ⟨hz,hn⟩

theorem exists_nonzero_in_sourceDomain_of_germ (f : ℂ → ℂ)
    (hne : ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0) :
    ∃ z ∈ complexFrozenSourceDomain, f z ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hne
  filter_upwards [eventually_mem_complexFrozenSourceDomain_at_zero] with z hz
  exact hn z hz

/-- Analytic continuation on the actual punctured source strip transfers
nonidentity to every prescribed nonempty open set of positive apertures. -/
theorem exists_source_nonzero_in_open_positive
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f complexFrozenSourceDomain)
    (hne : ∃ z ∈ complexFrozenSourceDomain, f z ≠ 0)
    {J : Set ℝ} (hJopen : IsOpen J) (hJne : J.Nonempty)
    (hJpos : J ⊆ Set.Ioi 0) : ∃ L ∈ J, f (L : ℂ) ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨L₀,hL₀J⟩ := hJne
  have hL₀pos : 0 < L₀ := hJpos hL₀J
  have hJnhds : ∀ᶠ L in 𝓝 L₀, L ∈ J := hJopen.mem_nhds hL₀J
  have hJevent : ∀ᶠ L in 𝓝[≠] L₀, L ∈ J :=
    hJnhds.filter_mono nhdsWithin_le_nhds
  have hreal : ∃ᶠ (L : ℝ) in 𝓝[≠] L₀, f (L : ℂ) = 0 := by
    apply Filter.Eventually.frequently
    filter_upwards [hJevent] with L hL
    exact hnone L hL
  have hcomplex : ∃ᶠ z in 𝓝[≠] (L₀ : ℂ), f z = 0 := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs,hxs,hzero⟩ := hreal
    refine ⟨fun n => (xs n : ℂ),?_,hzero⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    refine ⟨?_,?_⟩
    · rw [tendsto_ofReal_iff]
      exact hxs.1
    · filter_upwards [hxs.2] with n hn
      simpa using hn
  have hzero : Set.EqOn f 0 complexFrozenSourceDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf analyticOnNhd_const
      isPreconnected_complexFrozenSourceDomain
      ((ofReal_mem_complexFrozenSourceDomain_iff L₀).mpr hL₀pos.ne') hcomplex
  obtain ⟨z,hz,hzn⟩ := hne
  exact hzn (hzero hz)

theorem exists_source_nonzero_in_open_positive_of_germ
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f complexFrozenSourceDomain)
    (hne : ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0)
    {J : Set ℝ} (hJopen : IsOpen J) (hJne : J.Nonempty)
    (hJpos : J ⊆ Set.Ioi 0) : ∃ L ∈ J, f (L : ℂ) ≠ 0 :=
  exists_source_nonzero_in_open_positive f hf
    (exists_nonzero_in_sourceDomain_of_germ f hne) hJopen hJne hJpos

private theorem isOpen_positive_source_nonzero (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f complexFrozenSourceDomain) :
    IsOpen {L : ℝ | 0 < L ∧ f (L : ℂ) ≠ 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro L hL
  have hfT : Tendsto f (𝓝 (L : ℂ)) (𝓝 (f (L : ℂ))) :=
    (hf _ ((ofReal_mem_complexFrozenSourceDomain_iff L).mpr hL.1.ne')).continuousAt
  have hT := hfT.comp (Complex.continuous_ofReal.tendsto L)
  have hn : ({0}ᶜ : Set ℂ) ∈ 𝓝 (f (L : ℂ)) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hL.2)
  have hp : Set.Ioi (0 : ℝ) ∈ 𝓝 L := isOpen_Ioi.mem_nhds hL.1
  filter_upwards [hp,hT hn] with r hr hnr
  exact ⟨hr,by simpa using hnr⟩

/-- The finite family is fixed before selecting the physical aperture. -/
theorem exists_finite_source_nonzero_in_open_positive_of_germ
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) complexFrozenSourceDomain)
    (hne : ∀ i ∈ s, ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), f i z = 0)
    {J : Set ℝ} (hJopen : IsOpen J) (hJne : J.Nonempty)
    (hJpos : J ⊆ Set.Ioi 0) :
    ∃ L ∈ J, ∀ i ∈ s, f i (L : ℂ) ≠ 0 := by
  classical
  induction s using Finset.induction_on generalizing J with
  | empty =>
    obtain ⟨L,hL⟩ := hJne
    exact ⟨L,hL,by simp⟩
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) complexFrozenSourceDomain :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hns : ∀ i ∈ s, ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), f i z = 0 :=
      fun i hi => hne i (Finset.mem_insert_of_mem hi)
    obtain ⟨L₀,hL₀J,hL₀s⟩ := ih hfs hns hJopen hJne hJpos
    let U : Set ℝ := J ∩ ⋂ i ∈ s, {L : ℝ | 0 < L ∧ f i (L : ℂ) ≠ 0}
    have hUopen : IsOpen U := hJopen.inter (isOpen_biInter_finset
      (fun i hi => isOpen_positive_source_nonzero (f i) (hfs i hi)))
    have hU0 : L₀ ∈ U := by
      refine ⟨hL₀J,?_⟩
      simp only [Set.mem_iInter,Set.mem_setOf_eq]
      exact fun i hi => ⟨hJpos hL₀J,hL₀s i hi⟩
    obtain ⟨L,hLU,hLa⟩ := exists_source_nonzero_in_open_positive_of_germ (f a)
      (hf a (Finset.mem_insert_self a s)) (hne a (Finset.mem_insert_self a s))
      hUopen ⟨L₀,hU0⟩ (fun L hL => hJpos hL.1)
    refine ⟨L,hLU.1,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | his
    · exact hLa
    · have hLs := hLU.2
      simp only [Set.mem_iInter,Set.mem_setOf_eq] at hLs
      exact (hLs i his).2

end Zeta23.OPICARound4.RegularCells
