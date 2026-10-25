import Zeta23.OPICAFollowup.UniformSourceBounds
import Zeta23.OPICAFollowup.NearGapLimits
import Zeta23.OPICAFollowup.FiniteSpanSeparation

/- Independently authored from frozen A1--A3, HT2.1--HT2.3,
CT1.1--CT1.3 and R2-H2b, before elaborating any consumer.
No producer root statement or Validation statement was consulted. -/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators ENNReal FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.IndependentExpected
open Zeta23.OPICA Zeta23.CCM FiniteSpan

theorem expected_source_order_uniform_norms :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      (∀ k : ℕ, k ≤ 2 → ∀ x : ℝ,
        (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) +
          |iteratedDeriv k (sourceOrderFamily d) x| ≤
            Real.exp (C * (d + 1) * Real.log (d + 2))) ∧
      MemLp (integerDriveFamily d) 2 volume ∧
      ‖integerDriveFamilyL2 d‖ ≤ Real.exp (C * (d + 1) * Real.log (d + 2)) ∧
      sourceWeightedMoment 0 (1/2) (sourceOrderFamily d) = 0 ∧
      sourceWeightedMoment 1 (1/2) (sourceOrderFamily d) = 0 := by
  exact source_order_uniform_norms

theorem expected_native_field_theta_envelope :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ → ℝ,
      (∀ d, 0 < A d) ∧
      (∀ d, Real.log (1 + A d) ≤ C * (d + 1) * Real.log (d + 2)) ∧
      ∀ d : ℕ, ∀ t : ℝ, 0 ≤ t →
        |primeFieldFamily d t| ≤ A d * Real.exp (nativeZeroDisplacementSup * t) := by
  exact native_field_theta_envelope

theorem expected_near_gap_mass_bound
    (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth)
    (selfdual : ν.FourierSelfdual growth) (positiveOff : ν.negative integerLatticeᶜ = 0)
    (a R d : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (gap : ν.positive (Ioo (-a) a) = 0 ∧ ν.negative (Ioo (-a) a) = 0)
    (hR : 1 ≤ R) (hd : 0 < d) (hd2 : d ≤ 1/2) :
    ν.negative {x | |x| ≤ R ∧ d ≤ Metric.infDist x integerLattice} = 0 ∧
    ν.positive.real {x | |x| ≤ R ∧ d ≤ Metric.infDist x integerLattice} ≤
      Real.pi^2 * R^2 * (1-a) * ν.totalVariation.real (Icc (-1) 1) / (4*d^2) := by
  exact near_gap_mass_bound ν growth selfdual positiveOff a R d ha ha1 gap hR hd hd2

theorem expected_near_gap_controlled_limit_zero
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C * (1+R))
    (growth : ∀ n, (ν n).HasLinearGrowth)
    (selfdual : ∀ n, (ν n).FourierSelfdual (growth n))
    (positiveOff : ∀ n, (ν n).negative integerLatticeᶜ = 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n ∧ a n ≤ 1)
    (gap : ∀ n, (ν n).positive (Ioo (-a n) (a n)) = 0 ∧
      (ν n).negative (Ioo (-a n) (a n)) = 0)
    (sharp : Tendsto a atTop (𝓝 1)) :
    ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (ν n).distributionOfLinearGrowth (growth n) φ) atTop (𝓝 0) := by
  exact near_gap_controlled_limit_zero ν C common growth selfdual positiveOff a ha gap sharp

theorem expected_dilation_near_gap_family :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → L < Real.log 2 →
      (nearGapCombDistribution L =
        dilatedCombDistribution L + dilatedCombDistribution (-L) -
          ((2 * Real.cosh (L/2) : ℝ) : ℂ) • dilatedCombDistribution 0) ∧
      nearGapCombDistribution L ≠ 0 ∧
      𝓕 (nearGapCombDistribution L) = nearGapCombDistribution L ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).positive =
        (nearGapCombFamily L).positive ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).negative =
        (nearGapCombFamily L).negative ∧
      (nearGapCombFamily L).positive {0} = 0 ∧
      (nearGapCombFamily L).negative {0} = 0 ∧
      (nearGapCombFamily L).positive (Ioo (-Real.exp (-L)) (Real.exp (-L))) = 0 ∧
      (nearGapCombFamily L).negative (Ioo (-Real.exp (-L)) (Real.exp (-L))) = 0 ∧
      (nearGapCombFamily L).negative integerLatticeᶜ = 0 ∧
      (nearGapCombFamily L).positive {Real.exp (-L)} = ENNReal.ofReal (Real.exp (-L/2)) ∧
      (∀ R : ℝ, 0 ≤ R → (nearGapCombFamily L).totalVariation.real (Icc (-R) R) ≤ C*(1+R)) ∧
      (nearGapCombFamily L).integral sincSquared =
        2 * (Real.exp L - 1) / (Real.exp L)^(3/2 : ℝ) := by
  exact dilation_near_gap_family

theorem expected_dilation_normalized_limit_not_measure :
    ∃ T : TemperedDistribution ℝ ℂ,
      T ≠ 0 ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Tendsto (fun L : ℝ => (nearGapCombDistribution L φ) / (L : ℂ)^2)
          (𝓝[>] 0) (𝓝 (T φ))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        T φ = ∑' n : ℤ, ((n : ℂ)^2 * deriv (deriv φ) n + 2*(n : ℂ)*deriv φ n)) ∧
      (¬ ∃ μ : LocallyFiniteSignedMeasure, ∃ growth : μ.HasLinearGrowth,
        μ.distributionOfLinearGrowth growth = T) ∧
      (∀ M : ℝ, ∀ᶠ L : ℝ in 𝓝[>] 0,
        M < (nearGapCombFamily L).totalVariation.real (Icc (-2) 2) / L^2) := by
  exact dilation_normalized_limit_not_measure

theorem expected_fixed_basis_negative_mass_budget
    {n : ℕ} (basis : Fin n → List JetDatum)
    (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (independent : ∀ a : Fin n → ℝ,
      (zeroJetRealSpan (realBasisCombinationData basis a)).positive = 0 →
      (zeroJetRealSpan (realBasisCombinationData basis a)).negative = 0 → a = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Fin n → ℝ,
      c * Real.sqrt (∑ i, (a i)^2) ≤
        ∫ x : ℝ, sincSquared x ∂(zeroJetRealSpan (realBasisCombinationData basis a)).negative := by
  exact fixed_basis_negative_mass_budget basis valid independent

end Zeta23.OPICAFollowup.IndependentExpected
