import Zeta23.OPICAFollowup.NearGapLimits
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICA Zeta23.OPICAFollowup
example :
    Tendsto (fun L : ℝ => (∫ x, sincSquared x ∂(nearGapCombFamily L).positive) / L)
      (𝓝[>] 0) (𝓝 0) := by
  exact CT13Support.positive_sinc_mass_slope
