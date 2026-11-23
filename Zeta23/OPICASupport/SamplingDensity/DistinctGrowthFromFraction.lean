import Zeta23.OPICASupport.SamplingDensity.ResonanceCounting
import Zeta23.Assembly
import Zeta23.GammaFacts.Complete
import Zeta23.RvM.Statement

/-!
# A minimal positive-distinct-fraction supplier

Only a positive eventual fraction of distinct points is used.  Neither the
`3/4` numerical constant nor critical-line density is needed.  The actual zeta
distinct-fraction premise is deliberately left explicit; the unverified native
`Final`/`Unconditional` import closure is not imported by this module.
-/

noncomputable section

namespace Zeta23.OPICARound20

open Filter
open scoped Topology

theorem distinct_growth_of_positive_fraction
    (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) (a : ℝ) (ha : 0 < a)
    (hfrac : ∀ᶠ T : ℝ in atTop, a * (Z.N T (2 * T) : ℝ) ≤ (Z.Nd T (2 * T) : ℝ)) :
    DistinctWindowSuperlinear Z := by
  intro c b
  have hl : ∀ᶠ T : ℝ in atTop,
      (c + 1) * (4 * Real.pi) / a ≤ Zeta23.l T :=
    Assembly.tendsto_l_atTop.eventually_ge_atTop _
  have hgood : ∀ᶠ T : ℝ in atTop,
      0 < T ∧ c * T + b < (Z.Nd T (2 * T) : ℝ) := by
    filter_upwards [hfrac, Assembly.eventually_N_ge Z hRvM, hl,
      eventually_gt_atTop (max 0 b)] with T hfracT hNT hlT hT
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_left 0 b) hT
    have hbT : b < T := lt_of_le_of_lt (le_max_right 0 b) hT
    have hc : c + 1 ≤ a * Zeta23.l T / (4 * Real.pi) := by
      apply (le_div_iff₀ (show 0 < 4 * Real.pi by positivity)).mpr
      have := (div_le_iff₀ ha).mp hlT
      nlinarith
    have hscaled : (c + 1) * T ≤ a * (T * Zeta23.l T / (4 * Real.pi)) := by
      calc
        (c + 1) * T ≤ (a * Zeta23.l T / (4 * Real.pi)) * T :=
          mul_le_mul_of_nonneg_right hc hT0.le
        _ = a * (T * Zeta23.l T / (4 * Real.pi)) := by ring
    have hpositive := mul_le_mul_of_nonneg_left hNT ha.le
    refine ⟨hT0, ?_⟩
    linarith
  exact hgood.exists

/-- This is the existing unconditional native Riemann--von Mangoldt theorem
assembled from its already compiled analytic input, without importing `Final`. -/
theorem actual_zeta_riemannVonMangoldt : RiemannVonMangoldt zetaZeroConfig :=
  RvM.riemannVonMangoldt gammaFacts

/-- For actual zeta zeros, any positive distinct fraction supplies all required
nonresonant samples.  The distinct-fraction assumption remains explicit. -/
theorem actual_zeta_distinct_growth_of_positive_fraction
    (a : ℝ) (ha : 0 < a)
    (hfrac : ∀ᶠ T : ℝ in atTop, a * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ)) :
    DistinctWindowSuperlinear zetaZeroConfig := by
  apply distinct_growth_of_positive_fraction zetaZeroConfig actual_zeta_riemannVonMangoldt a ha
  simpa only [zetaZeroConfig, zetaZeros_N, zetaZeros_Nd] using hfrac

end Zeta23.OPICARound20
