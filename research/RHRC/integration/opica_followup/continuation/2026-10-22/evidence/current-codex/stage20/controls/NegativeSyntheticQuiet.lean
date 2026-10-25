import Zeta23.OPICAFollowup.Consumers
open Filter
open Zeta23 Zeta23.OPICAFollowup
example (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) : RiemannHypothesis := by
  have quiet : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ _n : ℕ in atTop, (0 : ℝ) ≤ epsilon :=
    fun _ hepsilon => Eventually.of_forall fun _ => hepsilon.le
  exact (quiet_balanced_observation_implies_native_cut time cofinal (Or.inl quiet)).2.2.2.2
