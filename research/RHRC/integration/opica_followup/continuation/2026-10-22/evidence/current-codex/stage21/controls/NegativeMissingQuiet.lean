import Zeta23.OPICAFollowup.Consumers
open Filter
open Zeta23 Zeta23.OPICAFollowup
example (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) : RiemannHypothesis := by
  exact (quiet_balanced_observation_implies_native_cut time cofinal).2.2.2.2
