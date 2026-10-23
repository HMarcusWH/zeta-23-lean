import Zeta23.OPICAFollowup.NearGapLimits
open Filter Set
open scoped Topology
open Zeta23.OPICA Zeta23.OPICAFollowup
-- (1) wrong sign of the first-derivative coefficient
theorem bad_sign (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun L : ℝ => nearGapCombDistribution L φ / (L : ℂ) ^ 2) (𝓝[≠] 0)
      (𝓝 (∑' n : ℤ, ((n : ℂ) ^ 2 * deriv (deriv φ) n - 2 * n * deriv φ n))) :=
  dilation_normalized_limit_not_measure.2.1 φ
-- (2) wrong normalization L instead of L^2
theorem bad_normalization (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun L : ℝ => nearGapCombDistribution L φ / (L : ℂ)) (𝓝[≠] 0)
      (𝓝 (∑' n : ℤ, ((n : ℂ) ^ 2 * deriv (deriv φ) n + 2 * n * deriv φ n))) :=
  dilation_normalized_limit_not_measure.2.1 φ
-- (3) the limit is not a measure
theorem bad_measure : ∃ μ : LocallyFiniteSignedMeasure, ∀ φ : SchwartzMap ℝ ℂ,
    (∫ x, φ x ∂μ.positive) - (∫ x, φ x ∂μ.negative) = ct1NormalizedLimit φ :=
  dilation_normalized_limit_not_measure.2.2.2.2.2.2.1
-- (4) the origin is not a non-order-zero point (coefficient cancelled)
theorem bad_origin_not_order_zero :
    ¬ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ, tsupport φ ⊆ Icc ((0 : ℤ) - 1 / 2 : ℝ) ((0 : ℤ) + 1 / 2) →
      ‖ct1NormalizedLimit φ‖ ≤ C * SchwartzMap.seminorm ℝ 0 0 φ :=
  dilation_normalized_limit_not_measure.2.2.2.2.2.1 0 (by decide)
