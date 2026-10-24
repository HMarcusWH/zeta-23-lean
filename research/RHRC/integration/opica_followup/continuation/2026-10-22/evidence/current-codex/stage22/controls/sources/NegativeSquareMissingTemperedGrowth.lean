import Zeta23.OPICAFollowup.SquareDefect

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.SquarePhysicalNegative
open Zeta23.OPICA

-- Expected rejection: a square of a general continuous vanishing function
-- need not have a unit gap without the actual plateau condition.
example (σ:LocallyFiniteComplexMeasure) : TemperedDistribution ℝ ℂ := by
  exact SquarePhysicalSupport.correctionDistribution σ

end Zeta23.OPICAFollowup.SquarePhysicalNegative
