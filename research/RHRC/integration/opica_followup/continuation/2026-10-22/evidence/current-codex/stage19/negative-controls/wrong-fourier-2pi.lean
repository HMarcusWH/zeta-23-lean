import Zeta23.OPICAFollowup.Consumers
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup

example (f : ℝ → ℂ) (ξ : ℝ) : logFourier f ξ = 𝓕 f ξ := by
  exact logFourier_eq_fourier f ξ
