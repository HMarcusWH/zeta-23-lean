import Mathlib.Data.Real.Basic

namespace Zeta23.ExceptionalZero

structure QuantitativeDetectorData where
  aperture : ℝ
  dimension : ℕ
  negativeMargin : ℝ
  aperture_pos : 0 < aperture
  negativeMargin_pos : 0 < negativeMargin

theorem QuantitativeDetectorData.margin_ne_zero
    (d : QuantitativeDetectorData) :
    d.negativeMargin ≠ 0 :=
  ne_of_gt d.negativeMargin_pos

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.QuantitativeDetectorData.margin_ne_zero
