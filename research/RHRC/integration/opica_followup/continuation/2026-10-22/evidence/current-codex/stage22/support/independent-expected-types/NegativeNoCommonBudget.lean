import CompactContinuousExtraction
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ENNReal FourierTransform SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup.IndependentCompactExtraction

/- Deliberately rejected gate: per-measure growth does not supply one
common local variation budget for passing from Schwartz to C_c tests. -/
example
    (ν : ℕ → LocallyFiniteSignedMeasure) (growth : ∀ n, (ν n).HasLinearGrowth)
    (schwartz : ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (ν n).distributionOfLinearGrowth (growth n) φ) atTop (𝓝 0))
    (f : ℝ → ℂ) (continuous : Continuous f) (compact : HasCompactSupport f) :
    Tendsto (fun n => signedCompactPairing (ν n) f) atTop (𝓝 0) := by
  refine schwartz_zero_implies_compact_continuous_zero ν 1 ?_ growth schwartz f continuous compact
