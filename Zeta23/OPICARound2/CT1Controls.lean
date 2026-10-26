import Zeta23.OPICAFollowup.NearGapLimits

/-! Scalar limits of the literal CT1 dilation family. This classification does
not extend to changed families or nonscalar transforms. -/

noncomputable section
open Set Filter
open scoped Topology
open Zeta23.OPICAFollowup

namespace Zeta23.OPICARound2

def CT1LocallyOrderZeroAt (U : TemperedDistribution ℝ ℂ) (x : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ,
    tsupport φ ⊆ Icc (x-r) (x+r) →
      ‖U φ‖ ≤ C * SchwartzMap.seminorm ℝ 0 0 φ

theorem ct1_normalized_sequence (L : ℕ → ℝ)
    (hL : ∀ j, L j ≠ 0) (hzero : Tendsto L atTop (𝓝 0))
    (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun j => nearGapCombDistribution (L j) φ / (L j : ℂ)^2)
      atTop (𝓝 (ct1NormalizedLimit φ)) := by
  have hpunct : Tendsto L atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hL⟩
  have h := dilation_normalized_limit_not_measure.2.1 φ
  rw [←ct1NormalizedLimit_apply] at h
  exact h.comp hpunct

/-- The nonzero test is a literal quadratic bump at the integer one. -/
theorem ct1_scalar_limit_classification (L : ℕ → ℝ) (c : ℕ → ℂ)
    (hL : ∀ j, L j ≠ 0) (hzero : Tendsto L atTop (𝓝 0))
    (U : TemperedDistribution ℝ ℂ)
    (hU : ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun j => c j * nearGapCombDistribution (L j) φ) atTop (𝓝 (U φ))) :
    ∃ a : ℂ, Tendsto (fun j => c j * (L j : ℂ)^2) atTop (𝓝 a) ∧
      U = a • ct1NormalizedLimit := by
  let φ₀ : SchwartzMap ℝ ℂ := ct1BumpTest 1 (ε:=1/4) (by norm_num)
  have htest : ct1NormalizedLimit φ₀ = 2 := by
    simpa [φ₀] using ct1NormalizedLimit_bumpTest 1 (ε:=1/4)
      (by norm_num) (by norm_num)
  let a : ℂ := U φ₀ / 2
  have hden := ct1_normalized_sequence L hL hzero φ₀
  rw [htest] at hden
  have hratio := (hU φ₀).div hden (by norm_num : (2:ℂ) ≠ 0)
  have hevent : ∀ᶠ j in atTop,
      nearGapCombDistribution (L j) φ₀ / (L j : ℂ)^2 ≠ 0 :=
    hden.eventually_ne (by norm_num : (2:ℂ) ≠ 0)
  have hscale : Tendsto (fun j => c j * (L j : ℂ)^2) atTop (𝓝 a) := by
    apply hratio.congr'
    filter_upwards [hevent] with j hj
    have hp : (L j : ℂ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL j)
    have hn : nearGapCombDistribution (L j) φ₀ ≠ 0 :=
      fun hn => hj (by rw [hn,zero_div])
    change (c j * nearGapCombDistribution (L j) φ₀) /
      (nearGapCombDistribution (L j) φ₀ / (L j : ℂ)^2) = c j * (L j : ℂ)^2
    field_simp [hn,hp]
  refine ⟨a,hscale,?_⟩
  ext φ
  have hprod := hscale.mul (ct1_normalized_sequence L hL hzero φ)
  have hprod' : Tendsto (fun j => c j * nearGapCombDistribution (L j) φ)
      atTop (𝓝 (a * ct1NormalizedLimit φ)) := by
    apply hprod.congr
    intro j
    have hp : (L j : ℂ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL j)
    field_simp [show (L j : ℂ) ≠ 0 by exact_mod_cast hL j]
  exact tendsto_nhds_unique (hU φ) hprod'

/-- An order-zero scalar multiple on any neighborhood of a nonzero integer
must vanish. No common variation bound for the approximating family is used. -/
theorem ct1_scalar_order_zero_at_integer {a : ℂ} (n : ℤ) (hn : n ≠ 0)
    (h : CT1LocallyOrderZeroAt (a • ct1NormalizedLimit) n) : a=0 := by
  by_contra ha
  obtain ⟨r,hr,C,hC⟩ := h
  let D : ℝ := max C 0
  have hD : 0≤D := le_max_right _ _
  have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have hnorm : 0 < ‖a * (2*(n:ℂ)^2)‖ := norm_pos_iff.mpr
    (mul_ne_zero ha (mul_ne_zero (by norm_num) (pow_ne_zero _ hn')))
  let ε : ℝ := min (min (r/2) (1/4)) (min 1 (‖a*(2*(n:ℂ)^2)‖/(2*(D+1))))
  have hε : 0<ε := lt_min (lt_min (by positivity) (by norm_num))
    (lt_min one_pos (by positivity))
  have hεr : ε≤r := (min_le_left _ _).trans
    ((min_le_left _ _).trans (by linarith))
  have hεhalf : ε≤1/2 := (min_le_left _ _).trans
    ((min_le_right _ _).trans (by norm_num))
  have hεone : ε≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεbound : ε≤‖a*(2*(n:ℂ)^2)‖/(2*(D+1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hs : tsupport (ct1BumpTest n hε) ⊆ Icc ((n:ℝ)-r) ((n:ℝ)+r) := by
    intro x hx
    have hb := ct1BumpProfile_tsupport n hε hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hb
    obtain ⟨hl,hu⟩ := abs_le.mp hb
    exact ⟨by linarith, by linarith⟩
  have htest := hC (ct1BumpTest n hε) hs
  change ‖a * ct1NormalizedLimit (ct1BumpTest n hε)‖ ≤ _ at htest
  rw [ct1NormalizedLimit_bumpTest n hε hεhalf] at htest
  have hS : 0≤SchwartzMap.seminorm ℝ 0 0 (ct1BumpTest n hε) := apply_nonneg _ _
  have hbound : ‖a*(2*(n:ℂ)^2)‖ ≤ D*ε^2 :=
    htest.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) hS).trans
      (mul_le_mul_of_nonneg_left (ct1BumpTest_seminorm_le n hε) hD))
  have hsmall : D*ε^2≤D*ε := mul_le_mul_of_nonneg_left (by nlinarith) hD
  have hscaled := (le_div_iff₀ (by positivity : 0<2*(D+1))).mp hεbound
  nlinarith

theorem ct1_order_zero_scalar_limit_is_zero (L : ℕ → ℝ) (c : ℕ → ℂ)
    (hL : ∀ j, L j ≠ 0) (hzero : Tendsto L atTop (𝓝 0))
    (U : TemperedDistribution ℝ ℂ)
    (hU : ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun j => c j * nearGapCombDistribution (L j) φ) atTop (𝓝 (U φ)))
    (n : ℤ) (hn : n ≠ 0) (horder : CT1LocallyOrderZeroAt U n) : U=0 := by
  obtain ⟨a,_,h⟩ := ct1_scalar_limit_classification L c hL hzero U hU
  rw [h] at horder ⊢
  rw [ct1_scalar_order_zero_at_integer n hn horder]
  ext φ
  change (0:ℂ) * ct1NormalizedLimit φ = 0
  simp

end Zeta23.OPICARound2
