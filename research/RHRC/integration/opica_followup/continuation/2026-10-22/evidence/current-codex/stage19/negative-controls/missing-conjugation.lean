import Zeta23.OPICAFollowup.Consumers
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup

example {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hR : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = 1 / (2 * π) * ∫ ξ : ℝ,
      logFourier sawtoothWeight ξ *
      (((ξ : ℂ) * I - 1 / 2) * logFourier (logUnitary (zeroProfile ρ)) ξ) := by
  exact (native_sample_stieltjes_identity hz h0 h1 hR).2.2.2.2.2.2.2.1
