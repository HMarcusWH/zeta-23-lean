import Zeta23.ExceptionalZero.FilteredResolvent
import Zeta23.ExceptionalZero.ZeroIsolation
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Metric Set

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

end Zeta23.ExceptionalZero
