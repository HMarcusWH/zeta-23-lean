import Zeta23.ExceptionalZero.FilteredResolvent
import Zeta23.ExceptionalZero.ZeroIsolation
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Metric Set Filter Topology

/-- Pole location associated to one filtered zero. -/
def filteredPolePoint (c : ℂ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  2 * ((ρ : ℂ) - c)

/-- The resolvent with one distinguished zero removed. -/
def filteredResolventRemainderTerm (φ : ZeroFilter) (c : ℂ)
    (ρ₀ ρ : zetaZeroConfig.carrier) (z : ℂ) : ℂ :=
  if ρ = ρ₀ then 0 else filteredResolventTerm φ c ρ z

/-- Infinite filtered resolvent after deleting the distinguished zero. -/
def filteredResolventRemainder (φ : ZeroFilter) (c : ℂ)
    (ρ₀ : zetaZeroConfig.carrier) (z : ℂ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, filteredResolventRemainderTerm φ c ρ₀ ρ z

/-- Distances between pole locations are exactly twice distances between the corresponding zeros. -/
theorem norm_filteredPolePoint_sub (c : ℂ) (ρ σ : zetaZeroConfig.carrier) :
    ‖filteredPolePoint c ρ - filteredPolePoint c σ‖ =
      2 * ‖(ρ : ℂ) - (σ : ℂ)‖ := by
  rw [show filteredPolePoint c ρ - filteredPolePoint c σ =
      (2 : ℂ) * ((ρ : ℂ) - (σ : ℂ)) by
    unfold filteredPolePoint
    ring]
  rw [norm_mul]
  norm_num

/-- An isolation radius for `ρ₀` gives a uniform denominator lower bound for every non-target
resolvent term throughout the corresponding ball around the target pole. -/
theorem isolationRadius_lt_norm_resolventDenom {c : ℂ} {ρ₀ : zetaZeroConfig.carrier}
    {r : ℝ} (_hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖)
    {z : ℂ} (hz : z ∈ ball (filteredPolePoint c ρ₀) r)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ≠ ρ₀) :
    r < ‖z - filteredPolePoint c ρ‖ := by
  have hpole : 2 * r ≤ ‖filteredPolePoint c ρ - filteredPolePoint c ρ₀‖ := by
    rw [norm_filteredPolePoint_sub]
    nlinarith [hiso ρ hρ]
  have hz' : ‖z - filteredPolePoint c ρ₀‖ < r := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hdecomp :
      filteredPolePoint c ρ - filteredPolePoint c ρ₀ =
        (filteredPolePoint c ρ - z) + (z - filteredPolePoint c ρ₀) := by
    ring
  have htri : ‖filteredPolePoint c ρ - filteredPolePoint c ρ₀‖ ≤
      ‖filteredPolePoint c ρ - z‖ + ‖z - filteredPolePoint c ρ₀‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  rw [norm_sub_rev (filteredPolePoint c ρ) z] at htri
  linarith

/-- Every non-target remainder summand is holomorphic on the isolation ball. -/
theorem differentiableOn_filteredResolventRemainderTerm
    {φ : ZeroFilter} {c : ℂ} {ρ₀ : zetaZeroConfig.carrier} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖)
    (ρ : zetaZeroConfig.carrier) :
    DifferentiableOn ℂ
      (fun z => filteredResolventRemainderTerm φ c ρ₀ ρ z)
      (ball (filteredPolePoint c ρ₀) r) := by
  intro z hz
  by_cases hρ : ρ = ρ₀
  · subst ρ
    have hzero :
        (fun w : ℂ => filteredResolventRemainderTerm φ c ρ₀ ρ₀ w) =
          (fun _ : ℂ => (0 : ℂ)) := by
      funext w
      rw [filteredResolventRemainderTerm, if_pos rfl]
    rw [hzero]
    fun_prop
  · simp only [filteredResolventRemainderTerm, if_neg hρ]
    have hnorm := isolationRadius_lt_norm_resolventDenom hr hiso hz hρ
    have hnorm' : 0 < ‖z - 2 * ((ρ : ℂ) - c)‖ := by
      have : 0 < ‖z - filteredPolePoint c ρ‖ := lt_trans hr hnorm
      simpa [filteredPolePoint] using this
    have hden : z - 2 * ((ρ : ℂ) - c) ≠ 0 := norm_pos_iff.mp hnorm'
    unfold filteredResolventTerm
    have hnum : DifferentiableAt ℂ (fun _ : ℂ => zeroFilterCoeff φ ρ) z := by fun_prop
    have hdenfun : DifferentiableAt ℂ (fun w : ℂ => w - 2 * ((ρ : ℂ) - c)) z := by fun_prop
    exact (hnum.div hdenfun hden).differentiableWithinAt

/-- The absolute coefficients give a summable uniform majorant for the deleted resolvent family on
an isolation ball. -/
theorem norm_filteredResolventRemainderTerm_le
    {φ : ZeroFilter} {c : ℂ} {ρ₀ : zetaZeroConfig.carrier} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖)
    (ρ : zetaZeroConfig.carrier) {z : ℂ}
    (hz : z ∈ ball (filteredPolePoint c ρ₀) r) :
    ‖filteredResolventRemainderTerm φ c ρ₀ ρ z‖ ≤
      (1 / r) * ‖zeroFilterCoeff φ ρ‖ := by
  by_cases hρ : ρ = ρ₀
  · subst ρ
    have hzero : filteredResolventRemainderTerm φ c ρ₀ ρ₀ z = 0 := by
      rw [filteredResolventRemainderTerm, if_pos rfl]
    rw [hzero, norm_zero]
    exact mul_nonneg (le_of_lt (one_div_pos.mpr hr)) (norm_nonneg _)
  · simp only [filteredResolventRemainderTerm, if_neg hρ]
    have hden := isolationRadius_lt_norm_resolventDenom hr hiso hz hρ
    have hden' : r < ‖z - 2 * ((ρ : ℂ) - c)‖ := by
      simpa [filteredPolePoint] using hden
    unfold filteredResolventTerm
    rw [norm_div]
    calc
      ‖zeroFilterCoeff φ ρ‖ / ‖z - 2 * ((ρ : ℂ) - c)‖
          ≤ ‖zeroFilterCoeff φ ρ‖ / r :=
        div_le_div_of_nonneg_left (norm_nonneg _) hr hden'.le
      _ = (1 / r) * ‖zeroFilterCoeff φ ρ‖ := by ring

/-- Pointwise summability of the deleted remainder on its isolation ball. -/
theorem summable_filteredResolventRemainderTerm
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} {ρ₀ : zetaZeroConfig.carrier} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖)
    {z : ℂ} (hz : z ∈ ball (filteredPolePoint c ρ₀) r) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      filteredResolventRemainderTerm φ c ρ₀ ρ z) := by
  unfold AbsolutelySummableZeroFilter at hφ
  exact Summable.of_norm_bounded
    (hφ.mul_left (1 / r))
    (fun ρ => norm_filteredResolventRemainderTerm_le hr hiso ρ hz)

/-- The full resolvent is summable on the isolation ball because it differs from the summable
remainder at exactly one index. -/
theorem summable_filteredResolventTerm_of_mem_isolationBall
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} {ρ₀ : zetaZeroConfig.carrier} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖)
    {z : ℂ} (hz : z ∈ ball (filteredPolePoint c ρ₀) r) :
    Summable (fun ρ : zetaZeroConfig.carrier => filteredResolventTerm φ c ρ z) := by
  have hrem := summable_filteredResolventRemainderTerm hφ hr hiso hz
  apply hrem.congr_cofinite
  filter_upwards [eventually_cofinite_ne ρ₀] with ρ hρ
  rw [filteredResolventRemainderTerm, if_neg hρ]

/-- After deleting one target zero, the full infinite filtered resolvent is holomorphic throughout
its isolation ball.  This is the local anti-cancellation seam: every other zero contributes only a
holomorphic remainder near the target pole. -/
theorem differentiableOn_filteredResolventRemainder
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} {ρ₀ : zetaZeroConfig.carrier} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖) :
    DifferentiableOn ℂ
      (filteredResolventRemainder φ c ρ₀)
      (ball (filteredPolePoint c ρ₀) r) := by
  unfold AbsolutelySummableZeroFilter at hφ
  have hu : Summable (fun ρ : zetaZeroConfig.carrier =>
      (1 / r) * ‖zeroFilterCoeff φ ρ‖) := hφ.mul_left (1 / r)
  exact Complex.differentiableOn_tsum_of_summable_norm
    (F := fun ρ z => filteredResolventRemainderTerm φ c ρ₀ ρ z)
    hu
    (fun ρ => differentiableOn_filteredResolventRemainderTerm hr hiso ρ)
    isOpen_ball
    (fun ρ z hz => norm_filteredResolventRemainderTerm_le hr hiso ρ hz)

/-- On the isolation ball, the legal infinite sum splits into the distinguished principal part plus
the holomorphic deleted remainder. -/
theorem filteredResolvent_eq_target_add_remainder
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} {ρ₀ : zetaZeroConfig.carrier} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖)
    {z : ℂ} (hz : z ∈ ball (filteredPolePoint c ρ₀) r) :
    filteredResolvent φ c z =
      filteredResolventTerm φ c ρ₀ z + filteredResolventRemainder φ c ρ₀ z := by
  classical
  have hsum := summable_filteredResolventTerm_of_mem_isolationBall hφ hr hiso hz
  have hsplit := hsum.tsum_eq_add_tsum_ite ρ₀
  unfold filteredResolvent filteredResolventRemainder
  simpa [filteredResolventRemainderTerm] using hsplit

/-- The distinguished zero is the exact principal part of the full filtered resolvent.  Multiplying
by `z-z₀` and approaching through the punctured plane recovers its multiplicity-weighted filter
coefficient.  A nonzero coefficient therefore cannot be cancelled by the rest of the zero family. -/
theorem filteredResolvent_principalPart_limit
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} {ρ₀ : zetaZeroConfig.carrier} {r : ℝ}
    (hr : 0 < r)
    (hiso : ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖) :
    Tendsto
      (fun z : ℂ => (z - filteredPolePoint c ρ₀) * filteredResolvent φ c z)
      (𝓝[≠] filteredPolePoint c ρ₀)
      (𝓝 (zeroFilterCoeff φ ρ₀)) := by
  let z₀ := filteredPolePoint c ρ₀
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hdiff := differentiableOn_filteredResolventRemainder
    (φ := φ) hφ (c := c) (ρ₀ := ρ₀) (r := r) hr hiso
  have hrem_cont : ContinuousAt (filteredResolventRemainder φ c ρ₀) z₀ := by
    have hwithin := hdiff z₀ hz₀
    exact (hwithin.differentiableAt (isOpen_ball.mem_nhds hz₀)).continuousAt
  have hrem_tend : Tendsto (filteredResolventRemainder φ c ρ₀)
      (𝓝[≠] z₀) (𝓝 (filteredResolventRemainder φ c ρ₀ z₀)) :=
    hrem_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hsub_tend : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
    have h := (continuousAt_id.sub continuousAt_const).tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have hprod_tend : Tendsto
      (fun z : ℂ => (z - z₀) * filteredResolventRemainder φ c ρ₀ z)
      (𝓝[≠] z₀) (𝓝 0) := by
    simpa using hsub_tend.mul hrem_tend
  have hmodel : Tendsto
      (fun z : ℂ => zeroFilterCoeff φ ρ₀ +
        (z - z₀) * filteredResolventRemainder φ c ρ₀ z)
      (𝓝[≠] z₀) (𝓝 (zeroFilterCoeff φ ρ₀)) := by
    simpa using tendsto_const_nhds.add hprod_tend
  refine hmodel.congr' ?_
  have hball : ball z₀ r ∈ 𝓝 z₀ := isOpen_ball.mem_nhds hz₀
  filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin]
    with z hz hzne
  have hdecomp := filteredResolvent_eq_target_add_remainder
    (φ := φ) hφ (c := c) (ρ₀ := ρ₀) (r := r) hr hiso hz
  rw [hdecomp]
  have hzne' : z ≠ z₀ := by
    simpa using hzne
  have hden : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne'
  have hden' : z - 2 * ((ρ₀ : ℂ) - c) ≠ 0 := by
    simpa [z₀, filteredPolePoint] using hden
  have htarget :
      (z - z₀) * filteredResolventTerm φ c ρ₀ z = zeroFilterCoeff φ ρ₀ := by
    unfold filteredResolventTerm
    rw [show z - z₀ = z - 2 * ((ρ₀ : ℂ) - c) by
      simp [z₀, filteredPolePoint]]
    field_simp [hden']
  rw [mul_add, htarget]

end Zeta23.ExceptionalZero
