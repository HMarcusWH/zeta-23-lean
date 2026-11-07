import Zeta23.CCM.LiftedPredecessorRegularity

noncomputable section
namespace Zeta23.OPICARound4
open CCM Complex Set Filter
open scoped Topology

/-- The existing connected log corridor gives nonvanishing in every open
positive aperture set for any analytic function with an actual nonzero point. -/
theorem exists_log_nonzero_in_open_positive
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f liftedFrozenRigidityDomain)
    (hne : ∃ z ∈ liftedFrozenRigidityDomain, f z ≠ 0)
    {J : Set ℝ} (hJopen : IsOpen J) (hJne : J.Nonempty)
    (hJpos : J ⊆ Set.Ioi 0) :
    ∃ L ∈ J, f (Real.log L : ℂ) ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨L₀, hL₀J⟩ := hJne
  have hL₀pos : 0 < L₀ := hJpos hL₀J
  have hJnhds : ∀ᶠ L in 𝓝 L₀, L ∈ J := hJopen.mem_nhds hL₀J
  have hJevent : ∀ᶠ L in 𝓝[≠] L₀, L ∈ J :=
    hJnhds.filter_mono nhdsWithin_le_nhds
  have hrealEvent : ∀ᶠ L in 𝓝[≠] L₀, L ∈ J ∧ f (Real.log L : ℂ) = 0 := by
    filter_upwards [hJevent] with L hLJ
    exact ⟨hLJ, hnone L hLJ⟩
  have hreal : ∃ᶠ L in 𝓝[≠] L₀, L ∈ J ∧ f (Real.log L : ℂ) = 0 :=
    hrealEvent.frequently
  have hcomplex : ∃ᶠ z in 𝓝[≠] (Real.log L₀ : ℂ), f z = 0 := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs_tendsto, hxs_zero⟩ := hreal
    refine ⟨fun n => (Real.log (xs n) : ℂ), ?_, fun n => (hxs_zero n).2⟩
    rw [tendsto_nhdsWithin_iff] at hxs_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact (Real.continuousAt_log hL₀pos.ne').tendsto.comp hxs_tendsto.1
    · filter_upwards [hxs_tendsto.2] with n hxsne
      have hxspos : 0 < xs n := hJpos (hxs_zero n).1
      have hlogne : Real.log (xs n) ≠ Real.log L₀ := by
        intro heq
        exact hxsne (Real.log_injOn_pos hxspos hL₀pos heq)
      simpa using hlogne
  have hzero : Set.EqOn f 0 liftedFrozenRigidityDomain :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf analyticOnNhd_const
      isPreconnected_liftedFrozenRigidityDomain
      (z₀ := (Real.log L₀ : ℂ))
      (ofReal_mem_liftedFrozenRigidityDomain (Real.log L₀)) hcomplex
  obtain ⟨z, hz, hzn⟩ := hne
  exact hzn (hzero hz)

private theorem isOpen_positive_log_nonzero
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f liftedFrozenRigidityDomain) :
    IsOpen {L : ℝ | 0 < L ∧ f (Real.log L : ℂ) ≠ 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro L hL
  have hfT : Tendsto f (𝓝 (Real.log L : ℂ)) (𝓝 (f (Real.log L : ℂ))) :=
    (hf _ (ofReal_mem_liftedFrozenRigidityDomain _)).continuousAt
  have hlT : Tendsto (fun r : ℝ => (Real.log r : ℂ)) (𝓝 L) (𝓝 (Real.log L : ℂ)) := by
    rw [tendsto_ofReal_iff]
    exact (Real.continuousAt_log hL.1.ne').tendsto
  have hn : ({0}ᶜ : Set ℂ) ∈ 𝓝 (f (Real.log L : ℂ)) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hL.2)
  have hp : Set.Ioi (0 : ℝ) ∈ 𝓝 L := isOpen_Ioi.mem_nhds hL.1
  have hnf := (hfT.comp hlT) hn
  filter_upwards [hp, hnf] with r hr hnr
  exact ⟨hr, by simpa using hnr⟩

/-- Finitely many actual nonidentity premises can be realized simultaneously
at one aperture in any prescribed nonempty open positive set. No common
nonzero point or pairwise spectral-separation premise is assumed. -/
theorem exists_finite_log_nonzero_in_open_positive
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) liftedFrozenRigidityDomain)
    (hne : ∀ i ∈ s, ∃ z ∈ liftedFrozenRigidityDomain, f i z ≠ 0)
    {J : Set ℝ} (hJopen : IsOpen J) (hJne : J.Nonempty)
    (hJpos : J ⊆ Set.Ioi 0) :
    ∃ L ∈ J, ∀ i ∈ s, f i (Real.log L : ℂ) ≠ 0 := by
  classical
  induction s using Finset.induction_on generalizing J with
  | empty =>
    obtain ⟨L, hL⟩ := hJne
    exact ⟨L, hL, by simp⟩
  | @insert a s ha ih =>
    have hfs : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) liftedFrozenRigidityDomain :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hns : ∀ i ∈ s, ∃ z ∈ liftedFrozenRigidityDomain, f i z ≠ 0 :=
      fun i hi => hne i (Finset.mem_insert_of_mem hi)
    obtain ⟨L₀, hL₀J, hL₀s⟩ := ih hfs hns hJopen hJne hJpos
    let U : Set ℝ := J ∩ ⋂ i ∈ s, {L : ℝ | 0 < L ∧ f i (Real.log L : ℂ) ≠ 0}
    have hUopen : IsOpen U := hJopen.inter (isOpen_biInter_finset
      (fun i hi => isOpen_positive_log_nonzero (f i) (hfs i hi)))
    have hU0 : L₀ ∈ U := by
      refine ⟨hL₀J, ?_⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact fun i hi => ⟨hJpos hL₀J, hL₀s i hi⟩
    have hUpos : U ⊆ Set.Ioi 0 := fun L hL => hJpos hL.1
    obtain ⟨L, hLU, hLa⟩ := exists_log_nonzero_in_open_positive (f a)
      (hf a (Finset.mem_insert_self a s)) (hne a (Finset.mem_insert_self a s))
      hUopen ⟨L₀, hU0⟩ hUpos
    refine ⟨L, hLU.1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | his
    · exact hLa
    · have hLs := hLU.2
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hLs
      exact (hLs i his).2

end Zeta23.OPICARound4
