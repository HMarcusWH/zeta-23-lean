import Zeta23.ExceptionalZero.FilteredPolePersistence
import Mathlib.Analysis.Meromorphic.Basic

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Metric Set Filter Topology

/-- Only finitely many filtered pole points meet any closed unit ball: local finiteness of the
zero configuration in the ordinate transfers to the pole lattice, because the pole map
`ρ ↦ 2(ρ - c)` moves imaginary parts affinely. -/
theorem finite_setOf_polePoint_near (c y : ℂ) :
    {ρ : zetaZeroConfig.carrier | ‖filteredPolePoint c ρ - y‖ ≤ 1}.Finite := by
  classical
  have hwin := zetaZeroConfig.finite_window
    ((y.im + 2 * c.im - 1) / 2 - 1) ((y.im + 2 * c.im + 1) / 2)
  have hpre : (Subtype.val ⁻¹'
      (zetaZeroConfig.carrier ∩
        {ρ : ℂ | (y.im + 2 * c.im - 1) / 2 - 1 < ρ.im ∧
          ρ.im ≤ (y.im + 2 * c.im + 1) / 2}) :
      Set zetaZeroConfig.carrier).Finite :=
    hwin.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro ρ hρ
  have him : |(filteredPolePoint c ρ - y).im| ≤ 1 :=
    le_trans (Complex.abs_im_le_norm _) hρ
  have himeq : (filteredPolePoint c ρ - y).im =
      2 * ((ρ : ℂ).im - c.im) - y.im := by
    simp [filteredPolePoint, Complex.mul_im]
  rw [himeq] at him
  have hb := abs_le.mp him
  refine ⟨ρ.2, ?_, ?_⟩
  · linarith [hb.1]
  · linarith [hb.2]

/-- Away from the pole lattice there is a uniform positive gap to every pole point. -/
theorem exists_pole_free_gap {c y : ℂ}
    (hy : ∀ ρ : zetaZeroConfig.carrier, filteredPolePoint c ρ ≠ y) :
    ∃ d : ℝ, 0 < d ∧
      ∀ ρ : zetaZeroConfig.carrier, d ≤ ‖filteredPolePoint c ρ - y‖ := by
  classical
  have hfin := finite_setOf_polePoint_near c y
  by_cases hne :
      {ρ : zetaZeroConfig.carrier | ‖filteredPolePoint c ρ - y‖ ≤ 1}.Nonempty
  · obtain ⟨ρm, hρm, hmin⟩ := Set.exists_min_image _
      (fun ρ : zetaZeroConfig.carrier => ‖filteredPolePoint c ρ - y‖) hfin hne
    have hpos : 0 < ‖filteredPolePoint c ρm - y‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hy ρm
    refine ⟨min ‖filteredPolePoint c ρm - y‖ 1, lt_min hpos one_pos, fun ρ => ?_⟩
    by_cases hρ : ‖filteredPolePoint c ρ - y‖ ≤ 1
    · exact le_trans (min_le_left _ _) (hmin ρ hρ)
    · exact le_trans (min_le_right _ _) (not_le.mp hρ).le
  · refine ⟨1, one_pos, fun ρ => ?_⟩
    by_contra h
    exact hne ⟨ρ, (lt_of_not_ge h).le⟩

/-- Off the pole lattice the filtered resolvent is analytic: the pole-free gap gives a uniform
denominator bound on a small ball, so the series is a locally uniform limit of holomorphic
functions. -/
theorem analyticAt_filteredResolvent_of_forall_ne
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ) {c y : ℂ}
    (hy : ∀ ρ : zetaZeroConfig.carrier, filteredPolePoint c ρ ≠ y) :
    AnalyticAt ℂ (filteredResolvent φ c) y := by
  obtain ⟨d, hd, hgap⟩ := exists_pole_free_gap hy
  have hhalf : 0 < d / 2 := by linarith
  have hden : ∀ (ρ : zetaZeroConfig.carrier), ∀ z ∈ ball y (d / 2),
      d / 2 ≤ ‖z - filteredPolePoint c ρ‖ := by
    intro ρ z hz
    have h1 := hgap ρ
    have h2 : ‖z - y‖ < d / 2 := by simpa [mem_ball, dist_eq_norm] using hz
    have h3 : ‖filteredPolePoint c ρ - y‖ ≤
        ‖filteredPolePoint c ρ - z‖ + ‖z - y‖ := by
      have := norm_add_le (filteredPolePoint c ρ - z) (z - y)
      rwa [sub_add_sub_cancel] at this
    have h4 : d / 2 ≤ ‖filteredPolePoint c ρ - z‖ := by linarith
    calc
      d / 2 ≤ ‖filteredPolePoint c ρ - z‖ := h4
      _ = ‖z - filteredPolePoint c ρ‖ := norm_sub_rev _ _
  have hu : Summable (fun ρ : zetaZeroConfig.carrier =>
      (2 / d) * ‖zeroFilterCoeff φ ρ‖) := hφ.mul_left _
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      DifferentiableOn ℂ (fun z => filteredResolventTerm φ c ρ z)
        (ball y (d / 2)) := by
    intro ρ z hz
    have hpos : 0 < ‖z - filteredPolePoint c ρ‖ := lt_of_lt_of_le hhalf (hden ρ z hz)
    have hne : z - 2 * ((ρ : ℂ) - c) ≠ 0 := by
      have hz' : z - filteredPolePoint c ρ ≠ 0 := norm_pos_iff.mp hpos
      simpa [filteredPolePoint] using hz'
    unfold filteredResolventTerm
    have hnum : DifferentiableAt ℂ (fun _ : ℂ => zeroFilterCoeff φ ρ) z := by fun_prop
    have hdenfun : DifferentiableAt ℂ (fun w : ℂ => w - 2 * ((ρ : ℂ) - c)) z := by
      fun_prop
    exact (hnum.div hdenfun hne).differentiableWithinAt
  have hboundterm : ∀ (ρ : zetaZeroConfig.carrier), ∀ z ∈ ball y (d / 2),
      ‖filteredResolventTerm φ c ρ z‖ ≤ (2 / d) * ‖zeroFilterCoeff φ ρ‖ := by
    intro ρ z hz
    have hdz : d / 2 ≤ ‖z - 2 * ((ρ : ℂ) - c)‖ := by
      simpa [filteredPolePoint] using hden ρ z hz
    unfold filteredResolventTerm
    rw [norm_div]
    calc
      ‖zeroFilterCoeff φ ρ‖ / ‖z - 2 * ((ρ : ℂ) - c)‖
          ≤ ‖zeroFilterCoeff φ ρ‖ / (d / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hhalf hdz
      _ = (2 / d) * ‖zeroFilterCoeff φ ρ‖ := by
        rw [div_div_eq_mul_div]
        ring
  have hdiff : DifferentiableOn ℂ (filteredResolvent φ c) (ball y (d / 2)) := by
    have := Complex.differentiableOn_tsum_of_summable_norm
      (F := fun (ρ : zetaZeroConfig.carrier) (z : ℂ) => filteredResolventTerm φ c ρ z)
      hu hterm isOpen_ball hboundterm
    exact this
  exact hdiff.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hhalf))

/-- The filtered resolvent of an absolutely summable filter is meromorphic at every point of the
plane: analytic off the pole lattice, and at each pole the sum of a simple rational principal part
and a holomorphic remainder. -/
theorem meromorphicAt_filteredResolvent
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ) (c y : ℂ) :
    MeromorphicAt (filteredResolvent φ c) y := by
  classical
  by_cases hy : ∃ ρ : zetaZeroConfig.carrier, filteredPolePoint c ρ = y
  · obtain ⟨ρ₀, hρ₀⟩ := hy
    subst hρ₀
    obtain ⟨r, hr, hiso⟩ := exists_zero_isolation_radius ρ₀
    have hrem_an : AnalyticAt ℂ (filteredResolventRemainder φ c ρ₀)
        (filteredPolePoint c ρ₀) :=
      (differentiableOn_filteredResolventRemainder (φ := φ) hφ (c := c)
        (ρ₀ := ρ₀) hr hiso).analyticAt
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    have htarget : MeromorphicAt (filteredResolventTerm φ c ρ₀)
        (filteredPolePoint c ρ₀) := by
      have hnum : MeromorphicAt (fun _ : ℂ => zeroFilterCoeff φ ρ₀)
          (filteredPolePoint c ρ₀) := analyticAt_const.meromorphicAt
      have hdenm : MeromorphicAt (fun z : ℂ => z - 2 * ((ρ₀ : ℂ) - c))
          (filteredPolePoint c ρ₀) :=
        (analyticAt_id.sub analyticAt_const).meromorphicAt
      apply (hnum.div hdenm).congr
      exact Eventually.of_forall fun z => rfl
    have hsum : MeromorphicAt
        (filteredResolventTerm φ c ρ₀ + filteredResolventRemainder φ c ρ₀)
        (filteredPolePoint c ρ₀) :=
      htarget.add hrem_an.meromorphicAt
    apply hsum.congr
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))]
      with z hz
    simp only [Pi.add_apply]
    exact (filteredResolvent_eq_target_add_remainder hφ hr hiso hz).symm
  · have hy' : ∀ ρ : zetaZeroConfig.carrier, filteredPolePoint c ρ ≠ y :=
      fun ρ hρ => hy ⟨ρ, hρ⟩
    exact (analyticAt_filteredResolvent_of_forall_ne hφ hy').meromorphicAt

/-- Global meromorphy of the filtered resolvent on any subset of the plane. -/
theorem meromorphicOn_filteredResolvent
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ) (c : ℂ) (U : Set ℂ) :
    MeromorphicOn (filteredResolvent φ c) U :=
  fun y _ => meromorphicAt_filteredResolvent hφ c y

end Zeta23.ExceptionalZero
