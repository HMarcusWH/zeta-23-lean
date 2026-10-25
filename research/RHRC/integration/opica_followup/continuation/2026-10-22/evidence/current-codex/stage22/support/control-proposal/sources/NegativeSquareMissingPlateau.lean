import Zeta23.OPICAFollowup.SquareDefect

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.SquarePhysicalNegative
open Zeta23.OPICA

-- Expected rejection: a square of a general continuous vanishing function
-- need not have a unit gap without the actual plateau condition.
example (h:ℝ→ℂ) (A:ℂ) (hc:Continuous h) :
    (squareGapJordan h A hc).positive (Ioo (-1) 1)=0 ∧
      (squareGapJordan h A hc).negative (Ioo (-1) 1)=0 := by
  exact squareGapJordan_gap hc A

-- Expected rejection: actual support on the lattice is indispensable to the
-- all-temperate-measure no-repair theorem, and cannot be silently omitted.

end Zeta23.OPICAFollowup.SquarePhysicalNegative
