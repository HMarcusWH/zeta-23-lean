import Zeta23.OPICAFollowup.Consumers
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup

example (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    nativeLogForce (hc.toSchwartzMap hφ) = -∫ t, (Real.exp (t / 2) : ℂ) * φ t := by
  exact (sawtooth_integrable_force_identity).2.2.2.2.2.1 φ hφ hc
