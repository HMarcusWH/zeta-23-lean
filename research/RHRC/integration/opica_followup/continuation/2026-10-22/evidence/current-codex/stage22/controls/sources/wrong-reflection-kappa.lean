import Zeta23.OPICAFollowup.Consumers
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup

example (ρ : ℂ) :
    spectralKappa (1 - ρ) = starRingEnd ℂ (spectralKappa ρ) := by
  simp only [spectralKappa]
  ring
