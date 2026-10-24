import Zeta23.OPICAFollowup.MovingSourceWindowRate
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICAFollowup
example (d : ℕ) :
    Tendsto (fun T : ℝ => nativeWindowLogRate d 1 T) atTop (𝓝 nativeZeroDisplacementSup) :=
  native_fixed_source_window_rate d 1 (by norm_num)
