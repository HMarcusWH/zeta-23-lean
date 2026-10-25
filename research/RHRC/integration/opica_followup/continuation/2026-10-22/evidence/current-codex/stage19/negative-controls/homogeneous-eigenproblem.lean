import Zeta23.OPICAFollowup.Consumers
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup

example {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    ∃ c : ℂ, ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hn⟩ :=
    actual_force_sampling_consumer hz h0 h1 hκ
  exact hn
