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
      (∀ k : ℕ, k ≤ 2 →
        (eLpNorm (iteratedDeriv k (sourceOrderFamily d)) ∞ volume).toReal +
          (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) ≤
            Real.exp (C * (d + 1) * Real.log (d + 2)) ∧
        eLpNorm (iteratedDeriv k (sourceOrderFamily d)) ∞ volume ≤
          ENNReal.ofReal (Real.exp (C * (d + 1) * Real.log (d + 2)))) ∧
      MemLp (integerDriveFamily d) 2 volume ∧
      ‖integerDriveFamilyL2 d‖ ≤ Real.exp (C * (d + 1) * Real.log (d + 2)) ∧
      (∀ t : ℝ, ∫ x : ℝ, uniform_nativeOrderLogDriveSummand d t x = 0) ∧
      sourceWeightedMoment 0 (1/2) (sourceOrderFamily d) = 0 ∧
      sourceWeightedMoment 1 (1/2) (sourceOrderFamily d) = 0 := by
  obtain ⟨C, hC, h⟩ := source_order_uniform_norms
  refine ⟨C, hC, fun d => ?_⟩
  obtain ⟨jet, lp, bound, cancellation⟩ := h d
  refine ⟨?_, ?_, lp, bound, cancellation,
    (sourceFamily_elementary_moments d 0 (by omega)).1,
    (sourceFamily_elementary_moments d 1 (by omega)).1⟩
  · intro k hk x
    simpa only [add_comm] using (jet k hk).1 x
  · intro k hk
    exact ⟨(jet k hk).2.2, (jet k hk).2.1⟩

theorem expected_native_field_theta_envelope :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ → ℝ,
      A = nativeFieldOrderConstant ∧
      (∀ d, 0 < A d) ∧
      (∀ d, Real.log (1 + A d) ≤ C * (d + 1) * Real.log (d + 2)) ∧
      ∀ d : ℕ, ∀ t : ℝ, 0 ≤ t →
        |primeFieldFamily d t| ≤ A d * Real.exp (nativeZeroDisplacementSup * t) := by
  obtain ⟨C, hC, h⟩ := native_field_theta_envelope
  exact ⟨C, hC, nativeFieldOrderConstant, rfl,
    fun d => (h d).1, fun d => (h d).2.2, fun d => (h d).2.1⟩

theorem expected_near_gap_mass_bound
    (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth)
    (selfdual : ν.FourierSelfdual growth) (positiveOff : ν.negative integerLatticeᶜ = 0)
    (a R d : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (gap : ν.positive (Ioo (-a) a) = 0 ∧ ν.negative (Ioo (-a) a) = 0)
    (hR : 1 ≤ R) (hd : 0 < d) (hd2 : d ≤ 1/2) :
    ν.negative {x | |x| ≤ R ∧ d ≤ Metric.infDist x integerLattice} = 0 ∧
    ν.positive.real {x | |x| ≤ R ∧ d ≤ Metric.infDist x integerLattice} ≤
      Real.pi^2 * R^2 * (1-a) * ν.totalVariation.real (Icc (-1) 1) / (4*d^2) := by
  obtain ⟨hn, hp⟩ := near_gap_mass_bound ν growth selfdual ha ha1 gap positiveOff hR hd hd2
  refine ⟨hn, ?_⟩
  convert hp using 1 <;> first | rfl | ring

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
  exact near_gap_controlled_limit_zero ν C common selfdual a
    (fun n => (ha n).1) (fun n => (ha n).2) gap positiveOff sharp

theorem expected_dilation_near_gap_family :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → L < Real.log 2 →
      (nearGapCombDistribution L =
        dilatedCombDistribution L + dilatedCombDistribution (-L) -
          ((2 * Real.cosh (L/2) : ℝ) : ℂ) • dilatedCombDistribution 0) ∧
      (∀ K : Set ℝ, ∀ hK : IsCompact K,
        localSignedCompactRestriction (nearGapCombFamily L) K hK =
          localSignedCompactRestriction (dilatedCombJordan L) K hK +
          localSignedCompactRestriction (dilatedCombJordan (-L)) K hK -
          (2 * Real.cosh (L/2)) • localSignedCompactRestriction (dilatedCombJordan 0) K hK) ∧
      (nearGapCombFamily L).HasLinearGrowth ∧
      nearGapCombDistribution L ≠ 0 ∧
      𝓕 (nearGapCombDistribution L) = nearGapCombDistribution L ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        nearGapCombDistribution L
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv φ) = nearGapCombDistribution L φ) ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).positive =
        (nearGapCombFamily L).positive ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).negative =
        (nearGapCombFamily L).negative ∧
      (nearGapCombFamily L).positive {0} = 0 ∧
      (nearGapCombFamily L).negative {0} = 0 ∧
      (nearGapCombFamily L).positive (Ioo (-Real.exp (-L)) (Real.exp (-L))) = 0 ∧
      (nearGapCombFamily L).negative (Ioo (-Real.exp (-L)) (Real.exp (-L))) = 0 ∧
      (1/2 < Real.exp (-L) ∧ Real.exp (-L) < 1) ∧
      (nearGapCombFamily L).negative integerLatticeᶜ = 0 ∧
      (nearGapCombFamily L).positive ≠ 0 ∧
      (nearGapCombFamily L).positive {Real.exp (-L)} = ENNReal.ofReal (Real.exp (-L/2)) ∧
      (nearGapCombFamily L).negative {Real.exp (-L)} = 0 ∧
      (∀ R : ℝ, 0 ≤ R → (nearGapCombFamily L).totalVariation.real (Icc (-R) R) ≤ C*(1+R)) := by
  refine ⟨18, by norm_num, fun L hL hL2 => ?_⟩
  obtain ⟨restriction, growth, common, selfdual, evenTest, gap, radius, off,
    origin, nonzero, evenJordan, edge, edgeNeg⟩ := dilation_near_gap_family L hL hL2
  have distNonzero : nearGapCombDistribution L ≠ 0 := by
    intro hz
    exact nonzero ((nearGapCombFamily L).parts_eq_zero_of_distribution_eq_zero growth hz).1
  have atom : (nearGapCombFamily L).positive {Real.exp (-L)} =
      ENNReal.ofReal (Real.exp (-L/2)) := by
    rw [← edge]
    exact (ENNReal.ofReal_toReal isCompact_singleton.measure_lt_top.ne).symm
  exact ⟨nearGapCombDistribution_eq_explicit L, restriction, growth, distNonzero, selfdual,
    evenTest, evenJordan.1, evenJordan.2, origin.1, origin.2, gap.1, gap.2,
    radius, off, nonzero, atom, edgeNeg, common.2⟩

theorem expected_dilation_normalized_limit_not_measure :
    ∃ T : TemperedDistribution ℝ ℂ,
      T = ct1NormalizedLimit ∧ T ≠ 0 ∧
      Tendsto (fun L : ℝ => ((L : ℂ)^2)⁻¹ • nearGapCombDistribution L)
        (𝓝[≠] 0) (𝓝 T) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Tendsto (fun L : ℝ => (nearGapCombDistribution L φ) / (L : ℂ)^2)
          (𝓝[≠] 0) (𝓝 (T φ))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        T φ = ∑' n : ℤ, ((n : ℂ)^2 * deriv (deriv φ) n + 2*(n : ℂ)*deriv φ n)) ∧
      (∀ φ : SchwartzMap ℝ ℂ, HasSum (fun n : ℤ =>
        ((n : ℂ)^2 • (TemperedDistribution.derivCLM ℂ)
          ((TemperedDistribution.derivCLM ℂ) (TemperedDistribution.delta (n : ℝ))) -
          (2*(n : ℂ)) • (TemperedDistribution.derivCLM ℂ)
            (TemperedDistribution.delta (n : ℝ))) φ) (T φ)) ∧
      (∀ n : ℤ, ∀ φ : SchwartzMap ℝ ℂ,
        tsupport (φ : ℝ → ℂ) ⊆ Icc ((n : ℝ)-1/2) ((n : ℝ)+1/2) →
        T φ = (n : ℂ)^2 * deriv (deriv φ) n + 2*(n : ℂ)*deriv φ n) ∧
      (∀ n : ℤ, n ≠ 0 → ¬ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ,
        tsupport (φ : ℝ → ℂ) ⊆ Icc ((n : ℝ)-1/2) ((n : ℝ)+1/2) →
        ‖T φ‖ ≤ C * SchwartzMap.seminorm ℝ 0 0 φ) ∧
      (¬ ∃ μ : LocallyFiniteSignedMeasure, ∀ φ : SchwartzMap ℝ ℂ,
        (∫ x : ℝ, φ x ∂μ.positive) - (∫ x : ℝ, φ x ∂μ.negative) = T φ) ∧
      (¬ ∃ μ : LocallyFiniteSignedMeasure, ∃ growth : μ.HasLinearGrowth,
        μ.distributionOfLinearGrowth growth = T) ∧
      Tendsto (fun L : ℝ => (nearGapCombFamily L).totalVariation.real (Icc (1/2) (3/2)) / L^2)
        (𝓝[>] 0) atTop ∧
      (∀ M : ℝ, ∀ᶠ L : ℝ in 𝓝[>] 0,
        M < (nearGapCombFamily L).totalVariation.real (Icc (-2) 2) / L^2) := by
  obtain ⟨topology, pairing, delta, localFormula, nonzero, order, measure, variation⟩ :=
    dilation_normalized_limit_not_measure
  refine ⟨ct1NormalizedLimit, rfl, nonzero, topology, ?_, ct1NormalizedLimit_apply,
    delta, localFormula, order, measure, ?_, variation, ?_⟩
  · intro φ
    simpa only [ct1NormalizedLimit_apply] using pairing φ
  · rintro ⟨μ, growth, hμ⟩
    apply measure
    refine ⟨μ, fun φ => ?_⟩
    simpa only [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply] using
      congrArg (fun S : TemperedDistribution ℝ ℂ => S φ) hμ
  · intro M
    filter_upwards [variation.eventually (eventually_gt_atTop M)] with L hL
    apply lt_of_lt_of_le hL
    apply div_le_div_of_nonneg_right _ (sq_nonneg L)
    exact measureReal_mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
      (h₂ := isCompact_Icc.measure_lt_top.ne)

theorem expected_fixed_basis_negative_mass_budget
    {n : ℕ} (basis : Fin n → List JetDatum)
    (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (independent : LinearIndependent ℝ (fun i =>
      (zeroJetRealSpan (basis i)).distributionOfLinearGrowth (zeroJetRealSpan_growth _ (valid i)))) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Fin n → ℝ,
      (c * Real.sqrt (∑ i, (a i)^2) ≤
        ∫ x : ℝ in integerLatticeᶜ, sincSquared x
          ∂(zeroJetRealSpan (realBasisCombinationData basis a)).negative) ∧
      c * Real.sqrt (∑ i, (a i)^2) ≤
        ∫ x : ℝ, sincSquared x ∂(zeroJetRealSpan (realBasisCombinationData basis a)).negative := by
  obtain ⟨c, hc, h⟩ := fixed_basis_negative_mass_budget basis valid independent
  refine ⟨c, hc, fun a => ?_⟩
  have bound := h (WithLp.toLp 2 a)
  have euclidean : ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (∑ i, (a i)^2) := by
    simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  have b : c * Real.sqrt (∑ i, (a i)^2) ≤
      ∫ x : ℝ in integerLatticeᶜ, sincSquared x
        ∂(zeroJetRealSpan (realBasisCombinationData basis a)).negative := by
    simpa only [euclidean, WithLp.ofLp_toLp] using bound
  refine ⟨b, ?_⟩
  have validA := realBasisCombination_valid basis valid a
  have growthA := zeroJetRealSpan_growth _ validA
  have gapA := zeroJetRealSpan_gap (realBasisCombinationData basis a)
  rw [← sincSquared_integral_compl_lattice _
    ((zeroJetRealSpan (realBasisCombinationData basis a)).negative_hasLinearGrowth growthA)
    (singleton_zero_of_unit_gap _ gapA.2)]
  exact b

/- The original, independently authored kernel premise and the canonical
interface quantify over exactly the same actual finite real combinations. -/
theorem actual_basis_independence_iff_Jordan_kernel
    {n : ℕ} (basis : Fin n → List JetDatum)
    (valid : ∀ i, ∀ j ∈ basis i, ValidJet j) :
    LinearIndependent ℝ (fun i =>
      (zeroJetRealSpan (basis i)).distributionOfLinearGrowth (zeroJetRealSpan_growth _ (valid i))) ↔
      ∀ a : Fin n → ℝ,
        (zeroJetRealSpan (realBasisCombinationData basis a)).positive = 0 →
        (zeroJetRealSpan (realBasisCombinationData basis a)).negative = 0 → a = 0 := by
  classical
  constructor
  · intro independent a hp hn
    have hz : (zeroJetRealSpan (realBasisCombinationData basis a)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid a)) = 0 := by
      ext φ
      simp only [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply, hp, hn,
        integral_zero_measure, sub_self, ContinuousLinearMap.zero_apply]
    rw [realBasisCombination_distribution basis valid a] at hz
    funext i
    exact Fintype.linearIndependent_iff.mp independent a hz i
  · intro kernel
    apply Fintype.linearIndependent_iff.mpr
    intro a hz i
    have hdist : (zeroJetRealSpan (realBasisCombinationData basis a)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid a)) = 0 := by
      rw [realBasisCombination_distribution basis valid a]
      exact hz
    have parts := (zeroJetRealSpan (realBasisCombinationData basis a)).parts_eq_zero_of_distribution_eq_zero
      (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid a)) hdist
    exact congrFun (kernel a parts.1 parts.2) i

/- Uniform tails used by the controlled-limit theorem, stated on the actual
total variation for every member of an arbitrary common-budget sequence. -/
theorem expected_controlled_uniform_tails
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C * (1+R))
    (M R : ℝ) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (f : ℝ → ℂ) (continuous : Continuous f)
    (decay : ∀ x, |x|^3 * ‖f x‖ ≤ M) :
    ∀ n, IntegrableOn f {x : ℝ | R ≤ |x|} (ν n).totalVariation ∧
      (∫ x : ℝ in {x | R ≤ |x|}, ‖f x‖ ∂(ν n).totalVariation) ≤ 4*C*M/R^2 := by
  intro n
  exact common_linear_cubic_tail _ C M R (common n) hM hR f continuous decay

#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_source_order_uniform_norms
#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_native_field_theta_envelope
#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_near_gap_mass_bound
#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_near_gap_controlled_limit_zero
#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_dilation_near_gap_family
#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_dilation_normalized_limit_not_measure
#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_fixed_basis_negative_mass_budget
#print axioms Zeta23.OPICAFollowup.IndependentExpected.actual_basis_independence_iff_Jordan_kernel
#print axioms Zeta23.OPICAFollowup.IndependentExpected.expected_controlled_uniform_tails

end Zeta23.OPICAFollowup.IndependentExpected
