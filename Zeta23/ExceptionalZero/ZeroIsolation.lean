import Zeta23.XiPrime.ExplicitFormula.ZeroFree

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set Filter Topology
open Zeta23.XiPrime

/-- Every distinct nontrivial zeta zero is separated by a positive Euclidean radius from all other
nontrivial zeros.  The proof is analytic rather than numerical: ξ has finite analytic order at the
target zero, hence locally factors as a power times a nonvanishing analytic function. -/
theorem exists_zero_isolation_radius (ρ₀ : zetaZeroConfig.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      r ≤ ‖(ρ : ℂ) - (ρ₀ : ℂ)‖ := by
  have hξ₂ : xi (2 : ℂ) ≠ 0 :=
    Zeta23.XiPrime.ZeroFree.xi_ne_zero_of_one_le_re (s := (2 : ℂ)) (by norm_num)
  have hwhole : AnalyticOnNhd ℂ xi (Set.univ : Set ℂ) := by
    intro z _
    exact xi_differentiable.analyticAt z
  have hpre : IsPreconnected (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).isPreconnected
  have hord₂ : analyticOrderAt xi (2 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hξ₂)]
    exact ENat.zero_ne_top
  have hord₀ : analyticOrderAt xi (ρ₀ : ℂ) ≠ ⊤ :=
    hwhole.analyticOrderAt_ne_top_of_isPreconnected hpre (Set.mem_univ _) (Set.mem_univ _) hord₂
  have han : AnalyticAt ℂ xi (ρ₀ : ℂ) := xi_differentiable.analyticAt _
  obtain ⟨g, hg, hg0, hfac⟩ := han.analyticOrderAt_ne_top.mp hord₀
  have hgne : ∀ᶠ z in 𝓝 (ρ₀ : ℂ), g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hpunct : ∀ᶠ z in 𝓝 (ρ₀ : ℂ), z ≠ (ρ₀ : ℂ) → xi z ≠ 0 := by
    filter_upwards [hgne, hfac] with z hgz hfz hz
    rw [hfz]
    simp only [smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) hgz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hpunct
  refine ⟨r, hr, fun ρ hρne => ?_⟩
  have hval : (ρ : ℂ) ≠ (ρ₀ : ℂ) := by
    intro h
    apply hρne
    exact Subtype.ext h
  by_contra hsep
  have hdist : dist (ρ : ℂ) (ρ₀ : ℂ) < r := by
    rw [dist_eq_norm]
    exact lt_of_not_ge hsep
  have hξne : xi (ρ : ℂ) ≠ 0 := hball hdist hval
  exact hξne ((Zeta23.XiPrime.ZeroFree.xi_eq_zero_iff (ρ : ℂ)).mpr ρ.2)

end Zeta23.ExceptionalZero
