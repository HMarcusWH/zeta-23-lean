import Zeta23.OPICAFollowup.ComplexLocalMeasures

/-! Full expected interface stated independently of the primary's inferred type.
The domain is the actual locally finite complex carrier, not finite whole-line
ComplexMeasure. Growth is one common bound for the sequence and its limit. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICARepairConsumers

example :
    (∀ μ : LocallyFiniteComplexMeasure, μ.totalVariation ≤ μ.variationControl ∧
      (μ.HasLinearGrowth ↔ LinearMassGrowth μ.totalVariation)) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ K L : Set ℝ,
      ∀ hK : IsCompact K, ∀ hL : IsCompact L,
      (μ.compactRestriction K hK).restrict L =
        μ.compactRestriction (K ∩ L) (hK.inter_right hL.isClosed)) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ K : Set ℝ, ∀ hK : IsCompact K,
      μ.totalVariation.restrict K = (μ.compactRestriction K hK).variation) ∧
    (∀ μ ν : LocallyFiniteComplexMeasure, ∀ c : ℂ, ∀ K : Set ℝ,
      ∀ hK : IsCompact K,
      (μ.add ν).compactRestriction K hK = μ.compactRestriction K hK + ν.compactRestriction K hK ∧
      (μ.scale c).compactRestriction K hK = c • μ.compactRestriction K hK) ∧
    Function.Injective
      (fun μ : {μ : LocallyFiniteComplexMeasure // μ.HasLinearGrowth} =>
        μ.val.distributionOfLinearGrowth μ.property) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ hμ : μ.HasLinearGrowth, ∀ f : SchwartzMap ℝ ℂ,
      μ.distributionOfLinearGrowth hμ f = μ.integral f ∧
      realifyComplexDistribution (μ.distributionOfLinearGrowth hμ) f =
        μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth hμ) f) ∧
    (∀ seq : ℕ → LocallyFiniteComplexMeasure, ∀ μ : LocallyFiniteComplexMeasure,
      LocalVariationConvergence seq μ → ∀ f : ℝ → ℂ,
      Continuous f → HasCompactSupport f →
      Tendsto (fun n => (seq n).integral f) atTop (𝓝 (μ.integral f))) ∧
    (∀ seq : ℕ → LocallyFiniteComplexMeasure, ∀ μ : LocallyFiniteComplexMeasure,
      LocalVariationConvergence seq μ → ∀ C : ℝ,
      (∀ n, CommonLinearMassBound C (seq n).variationControl) →
      CommonLinearMassBound C μ.variationControl → ∀ f : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (seq n).integral f) atTop (𝓝 (μ.integral f))) := by
  exact complex_local_measure_embedding_faithful

/-- Growth of genuine Euclidean variation is sufficient: coordinate control
is derived with the required factor two rather than identified with it. -/
example (μ : LocallyFiniteComplexMeasure) (h : LinearMassGrowth μ.totalVariation) :
    μ.HasLinearGrowth := by
  exact μ.hasLinearGrowth_iff_totalVariation.mpr h

/-- Truly imaginary scalar, arbitrary compact sets, no whole-line finiteness. -/
example (μ : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    (μ.scale I).compactRestriction K hK = I • μ.compactRestriction K hK := by
  exact μ.compactRestriction_scale I K hK

example (μ ν : LocallyFiniteComplexMeasure) (hμ : μ.HasLinearGrowth)
    (hν : ν.HasLinearGrowth) (c : ℂ) :
    (μ.add (ν.scale c)).HasLinearGrowth := by
  exact μ.hasLinearGrowth_add (ν.scale c) hμ (ν.hasLinearGrowth_scale hν c)

example (seq : ℕ → LocallyFiniteComplexMeasure) (μ : LocallyFiniteComplexMeasure)
    (hlocal : LocalVariationConvergence seq μ) (C : ℝ)
    (hseq : ∀ n, CommonLinearMassBound C (seq n).variationControl)
    (hμ : CommonLinearMassBound C μ.variationControl) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (seq n).distributionOfLinearGrowth (hseq n).linearGrowth f)
      atTop (𝓝 (μ.distributionOfLinearGrowth hμ.linearGrowth f)) := by
  exact hlocal.tendsto_schwartz_common_growth C hseq hμ f

/-- The quantitative tail comes from the same fixed growth and test budgets. -/
example (μ : LocallyFiniteComplexMeasure) (C M R : ℝ)
    (hg : CommonLinearMassBound C μ.variationControl) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (f : SchwartzMap ℝ ℂ) (hd : ∀ x, |x|^3 * ‖f x‖ ≤ M) :
    ‖μ.integral f - finiteComplexIntegral
      (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f‖ ≤ 4*C*M/R^2 := by
  exact complexIntegral_cutoff_error μ C M R hg hM hR f hd

#print axioms Zeta23.OPICAFollowup.complex_local_measure_embedding_faithful
#print axioms Zeta23.OPICAFollowup.LocalVariationConvergence.tendsto_schwartz_common_growth
#print axioms Zeta23.OPICAFollowup.common_linear_cubic_tail
#print axioms Zeta23.OPICAFollowup.LocallyFiniteComplexMeasure.hasLinearGrowth_iff_totalVariation
end OPICARepairConsumers
