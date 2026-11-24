import Zeta23.Unconditional
import Zeta23.OPICASupport.SamplingDensity.DistinctGrowthFromFraction

/-!
This common-pin compatibility adapter uses the actual native distinct-zero
count Ndist. The only numerical input retained from thmC₀ is the positive
one-half fraction obtained at epsilon = one quarter. No C1 or RH premise is
introduced. Acceptance requires the separate compilation and proof receipts.
-/

noncomputable section

namespace Zeta23.OPICARound20.DensityCompatibility

open Filter
open scoped Topology

theorem eventually_half_distinct :
    ∀ᶠ T : ℝ in atTop,
      (1 / 2 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.thmC₀ (1 / 4 : ℝ) (by norm_num)
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hc : (3 / 4 - (1 / 4 : ℝ)) = 1 / 2 := by norm_num
  simpa only [hc] using hT₀ T hT

theorem actual_distinct_window_superlinear :
    DistinctWindowSuperlinear zetaZeroConfig :=
  actual_zeta_distinct_growth_of_positive_fraction (1 / 2) (by norm_num)
    eventually_half_distinct

theorem actual_nonresonant_zero_samples {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ∃ ρ : Fin n → zetaZeroConfig.carrier,
      Function.Injective (fun j => gammaOf (ρ j)) ∧
      ∀ j, Complex.exp (Complex.I * gammaOf (ρ j) * (L : ℂ)) ≠ 1 :=
  exists_nonresonant_zero_samples_of_distinct_growth zetaZeroConfig
    actual_distinct_window_superlinear hL n

end Zeta23.OPICARound20.DensityCompatibility
