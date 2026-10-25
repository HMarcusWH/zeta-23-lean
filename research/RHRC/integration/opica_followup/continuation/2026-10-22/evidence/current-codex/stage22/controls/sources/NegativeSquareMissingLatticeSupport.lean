import Zeta23.OPICAFollowup.SquareDefect

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.SquarePhysicalNegative
open Zeta23.OPICA

-- Expected rejection: a square of a general continuous vanishing function
-- need not have a unit gap without the actual plateau condition.
example {h:ℝ→ℂ} {A:ℂ} (hev:∀x,h (-x)=h x) (hc:Continuous h)
    (hi:Integrable h) (h2:MemLp h 2) (hs:𝓕 h=h)
    (hv:Tendsto h (cocompact ℝ) (𝓝 0)) (hp:∀x,|x|≤1→h x=A) (hn:h≠0)
    (σ:LocallyFiniteComplexMeasure) [σ.totalVariation.HasTemperateGrowth] :
    𝓕 ((squareGapJordan h A hc).distributionOfLinearGrowth (squareGapJordan_growth hc hv A)+
      SquarePhysicalSupport.correctionDistribution σ) ≠
      (squareGapJordan h A hc).distributionOfLinearGrowth (squareGapJordan_growth hc hv A)+
        SquarePhysicalSupport.correctionDistribution σ := by
  exact square_actual_no_tempered_measure_repair hev hc hi h2 hs hv hp hn σ

-- Expected rejection: no tempered-distribution embedding of an arbitrary
-- locally finite complex measure is invented without its genuine growth domain.

end Zeta23.OPICAFollowup.SquarePhysicalNegative
