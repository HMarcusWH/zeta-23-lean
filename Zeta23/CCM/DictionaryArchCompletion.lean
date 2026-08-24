import Zeta23.CCM.DictionaryArchLaplace

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators

/-! # Completion of the deterministic archimedean bridge

This file continues the exact v0.7 PR #42 proof order downstream of the
compiler-proved digamma-series and Laplace/Tonelli lemmas.  It remains zero-free
and introduces no explicit-formula hypothesis.
-/

/-- For positive physical coordinate `x`, the Laplace summands collapse to the
closed archimedean density by an ordinary geometric series. -/
theorem tsum_archPhysicalSeriesTerm_eq_archDensity
    (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    (∑' m : ℕ, archPhysicalSeriesTerm τ m x) =
      2 * archDensity x * (1 - Real.cos (τ * x)) := by
  have hq : ‖Real.exp (-2 * x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom :
      (∑' m : ℕ, (Real.exp (-2 * x)) ^ m) =
        (1 - Real.exp (-2 * x))⁻¹ :=
    tsum_geometric_of_norm_lt_one hq
  have hterm (m : ℕ) :
      Real.exp (-(2 * ((m : ℝ) + 1 / 4)) * x) =
        Real.exp (-x / 2) * (Real.exp (-2 * x)) ^ m := by
    calc
      Real.exp (-(2 * ((m : ℝ) + 1 / 4)) * x) =
          Real.exp (-x / 2 + (m : ℝ) * (-2 * x)) := by
            congr 1
            ring
      _ = Real.exp (-x / 2) * Real.exp ((m : ℝ) * (-2 * x)) := by
            rw [Real.exp_add]
      _ = Real.exp (-x / 2) * (Real.exp (-2 * x)) ^ m := by
            rw [Real.exp_nat_mul]
  have hseries :
      (∑' m : ℕ, archPhysicalSeriesTerm τ m x) =
        (2 * Real.exp (-x / 2) * (1 - Real.cos (τ * x))) *
          (∑' m : ℕ, (Real.exp (-2 * x)) ^ m) := by
    calc
      (∑' m : ℕ, archPhysicalSeriesTerm τ m x) =
          ∑' m : ℕ,
            (2 * Real.exp (-x / 2) * (1 - Real.cos (τ * x))) *
              (Real.exp (-2 * x)) ^ m := by
        apply tsum_congr
        intro m
        unfold archPhysicalSeriesTerm
        rw [hterm m]
        ring
      _ = (2 * Real.exp (-x / 2) * (1 - Real.cos (τ * x))) *
          (∑' m : ℕ, (Real.exp (-2 * x)) ^ m) := by
        rw [tsum_mul_left]
  have hq_lt : Real.exp (-2 * x) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hqne : 1 - Real.exp (-2 * x) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt hq_lt).symm
  have hdenpos : 0 < Real.exp x - Real.exp (-x) := by
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hdenne : Real.exp x - Real.exp (-x) ≠ 0 := ne_of_gt hdenpos
  have hA : Real.exp (-x / 2) * Real.exp x = Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hB :
      Real.exp (-x / 2) * Real.exp (-x) =
        Real.exp (x / 2) * Real.exp (-2 * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hdensity :
      Real.exp (-x / 2) * (1 - Real.exp (-2 * x))⁻¹ = archDensity x := by
    unfold archDensity
    field_simp [hqne, hdenne]
    rw [mul_sub, mul_sub, mul_one, hA, hB]
  rw [hseries, hgeom]
  calc
    (2 * Real.exp (-x / 2) * (1 - Real.cos (τ * x))) *
        (1 - Real.exp (-2 * x))⁻¹ =
      2 * (Real.exp (-x / 2) * (1 - Real.exp (-2 * x))⁻¹) *
        (1 - Real.cos (τ * x)) := by ring
    _ = 2 * archDensity x * (1 - Real.cos (τ * x)) := by
      rw [hdensity]

/-- Exact physical-space representation of the gamma-density difference.  This is
Phase B of the v0.7 archimedean spine and is derived only from the already-proved
digamma series plus the certified Tonelli interchange. -/
theorem mu_sub_mu_zero_eq_archDensity_integral (τ : ℝ) :
    Zeta23.mu τ - Zeta23.mu 0 =
      (1 / Real.pi) *
        ∫ x : ℝ in Ioi 0, archDensity x * (1 - Real.cos (τ * x)) := by
  rw [mu_sub_mu_zero_eq_archDigammaAllSeries]
  simp_rw [← integral_archPhysicalSeriesTerm_Ioi τ]
  rw [tsum_integral_archPhysicalSeriesTerm_eq_integral_tsum τ]
  have hclosed :
      (∫ x : ℝ in Ioi 0, ∑' m : ℕ, archPhysicalSeriesTerm τ m x) =
        ∫ x : ℝ in Ioi 0,
          2 * archDensity x * (1 - Real.cos (τ * x)) := by
    apply integral_congr_ae
    filter_upwards with x hx
    exact tsum_archPhysicalSeriesTerm_eq_archDensity τ hx
  rw [hclosed]
  have hfactor :
      (∫ x : ℝ in Ioi 0,
          2 * archDensity x * (1 - Real.cos (τ * x))) =
        2 * ∫ x : ℝ in Ioi 0,
          archDensity x * (1 - Real.cos (τ * x)) := by
    have hfun :
        (fun x : ℝ => 2 * archDensity x * (1 - Real.cos (τ * x))) =
          fun x : ℝ => 2 * (archDensity x * (1 - Real.cos (τ * x))) := by
      funext x
      ring
    rw [hfun, integral_const_mul]
  rw [hfactor]
  field_simp [Real.pi_ne_zero]

end Zeta23.CCM
