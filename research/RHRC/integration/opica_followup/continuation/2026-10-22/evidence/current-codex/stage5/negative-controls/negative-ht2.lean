import Zeta23.OPICAFollowup.NearGapLimits
open Filter MeasureTheory Set
open scoped Topology
open Zeta23.OPICA Zeta23.OPICAFollowup
-- (1) gaps tending to 1/2 instead of 1 must not give the limit
theorem bad_half_gap_limit (nu : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (hC : ∀ n, CommonLinearMassBound C (nu n).totalVariation)
    (hself : ∀ n, (nu n).FourierSelfdual (hC n).linearGrowth)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hgap : ∀ n, hasNearGap (nu n) (a n)) (hoff : ∀ n, (nu n).OffLatticeNonnegative)
    (hlim : Tendsto a atTop (𝓝 (1 / 2))) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (nu n).distributionOfLinearGrowth (hC n).linearGrowth φ) atTop (𝓝 0) :=
  near_gap_controlled_limit_zero nu C hC hself a ha ha1 hgap hoff hlim φ
-- (2) the root is not total-variation convergence
theorem bad_total_variation_limit (nu : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (hC : ∀ n, CommonLinearMassBound C (nu n).totalVariation)
    (hself : ∀ n, (nu n).FourierSelfdual (hC n).linearGrowth)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hgap : ∀ n, hasNearGap (nu n) (a n)) (hoff : ∀ n, (nu n).OffLatticeNonnegative)
    (hlim : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun n => (nu n).totalVariation.real (Icc (-1) 1)) atTop (𝓝 0) :=
  near_gap_controlled_limit_zero nu C hC hself a ha ha1 hgap hoff hlim
-- (3) off-lattice nonnegativity cannot be dropped
theorem bad_no_offlattice (nu : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (hC : ∀ n, CommonLinearMassBound C (nu n).totalVariation)
    (hself : ∀ n, (nu n).FourierSelfdual (hC n).linearGrowth)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hgap : ∀ n, hasNearGap (nu n) (a n))
    (hlim : Tendsto a atTop (𝓝 1)) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (nu n).distributionOfLinearGrowth (hC n).linearGrowth φ) atTop (𝓝 0) :=
  near_gap_controlled_limit_zero nu C hC hself a ha ha1 hgap (fun n => by assumption) hlim φ
-- (4) a fixed CT1 member is not the zero distribution
theorem bad_CT1_member_zero (L : ℝ) (hL : 0 < L) (hu : L < Real.log 2) :
    nearGapCombDistribution L = 0 := by
  exact (nearGapCombFamily_controlled_limit (fun _ => L) (fun _ => hL) (fun _ => hu)
    tendsto_const_nhds)
