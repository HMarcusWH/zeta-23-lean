import Zeta23.OPICAFollowup.MovingSourceWindowRate
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.OPICAFollowup
example (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) (d : ℕ → ℕ)
    (C : ℝ) (hC : 1 < C) :
    Tendsto (fun n => nativeWindowLogRate (d n) C (time n)) atTop (𝓝 nativeZeroDisplacementSup) :=
  native_slow_source_window_rate time cofinal d C hC
