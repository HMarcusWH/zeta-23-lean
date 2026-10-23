import Zeta23.OPICAFollowup.WeightedMixing

/- Independent consumers for the original R1-HT1 roots
`weighted_mobius_inverse`, `weighted_mixture_sharp_gap` and `weighted_gap_leakage`.

Definition audits pin the lattice measures N, M⁺, M⁻ and the weighted norm to
their explicit formulas. The root types are restated in full. Actual-domain
consumers use genuine point-mass mixers built from canonical Jordan pairs:
the leakage lower bound is strictly positive for δ₋₁, and the sharp-gap
hypotheses are satisfied by δ₀, whose mixture is exactly the integer comb
(so the sharp-gap theorem is not vacuous). -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology FourierTransform SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICAWeightedInverseIndependent

/-! ### Definition audits -/

theorem audit_integerLogComb : integerLogComb =
    Measure.sum (fun k : ℕ => (if k = 0 then 0 else ENNReal.ofReal (Real.sqrt (k : ℝ))⁻¹) •
      Measure.dirac (Real.log k)) := rfl

theorem audit_moebiusPlusComb : moebiusPlusComb =
    Measure.sum (fun k : ℕ => (if ArithmeticFunction.moebius k = 1 then
      (if k = 0 then 0 else ENNReal.ofReal (Real.sqrt (k : ℝ))⁻¹) else 0) •
      Measure.dirac (Real.log k)) := rfl

theorem audit_moebiusMinusComb : moebiusMinusComb =
    Measure.sum (fun k : ℕ => (if ArithmeticFunction.moebius k = -1 then
      (if k = 0 then 0 else ENNReal.ofReal (Real.sqrt (k : ℝ))⁻¹) else 0) •
      Measure.dirac (Real.log k)) := rfl

theorem audit_weightedLogNorm (a : ℝ) (ρ : Measure ℝ) :
    weightedLogNorm a ρ = ∫⁻ y, ENNReal.ofReal (Real.exp (-a * y)) ∂ρ := rfl

theorem audit_mixtureDensity (h : ℝ → ℂ) (x : ℝ) :
    mixtureDensity h x = ((Real.sqrt x)⁻¹ : ℝ) * ∑' n : ℕ,
      ((if n = 0 then 0 else (Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * h (Real.log (x / n)) := rfl

/-! ### Restated roots -/

theorem expected_moebius_lattice_identity :
    moebiusPlusComb ∗ integerLogComb = Measure.dirac 0 + moebiusMinusComb ∗ integerLogComb :=
  (weighted_mobius_inverse (⟨localJordanDifference 0 0, localJordanDifference 0 0⟩) 1
    (by norm_num) (by
      refine lt_of_le_of_lt (lintegral_mono' (LocallyFiniteComplexMeasure.totalVariation_le_control _)
        le_rfl) ?_
      change ∫⁻ t, ENNReal.ofReal (Real.exp (1 * |t|)) ∂(((0 - 0) + (0 - 0)) + ((0 - 0) + (0 - 0))) < ∞
      simp)).2.2.2.1

theorem expected_weighted_mobius_inverse_real (σ : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞) :
    positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
        integerLogComb ∗ σ.rePart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
        integerLogComb ∗ σ.rePart.positive ∧
    σ.rePart.positive +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive) =
      σ.rePart.negative +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative) ∧
    weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) =
        ENNReal.ofReal (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) ∧
    ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
      riemannZeta ((a + 1 / 2 : ℝ) : ℂ) / riemannZeta ((2 * a + 1 : ℝ) : ℂ) := by
  obtain ⟨-, hre, -, -, hinv, -, -, -, -, -, hM⟩ := weighted_mobius_inverse σ a ha hm
  exact ⟨hre, hinv, hM.1, hM.2⟩

theorem expected_weighted_mixture_sharp_gap (σ : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞)
    (hself : 𝓕 ((weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm)) =
      (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm))
    (hgap : (weightedDilationMixture σ a ha.le hm).variationControl (Ioo (-1) 1 \ {0}) = 0) :
    σ.variationControl ({0}ᶜ) = 0 ∧
    (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm) =
      σ.integral (fun _ => 1) • dilatedCombDistribution 0 ∧
    ((weightedDilationMixture σ a ha.le hm).compactRestriction {0} isCompact_singleton {0} = 0 →
      (weightedDilationMixture σ a ha.le hm).variationControl = 0) := by
  obtain ⟨-, h1, h2, -, h3⟩ := weighted_mixture_sharp_gap σ a ha hm hself hgap
  exact ⟨h1, h2, fun h0 => (h3 h0).2.2⟩

theorem expected_weighted_gap_leakage_real (σ : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞) :
    ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t))
          ∂(σ.rePart.positive + σ.rePart.negative) ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂((weightedDilationMixture σ a ha.le hm).rePart.positive +
          (weightedDilationMixture σ a ha.le hm).rePart.negative) :=
  (weighted_gap_leakage.1 σ a ha hm).1

/-! ### Actual point-mass mixers -/

/-- The genuine complex point mass δ_x (canonical Jordan pairs). -/
def pointMixer (x : ℝ) : LocallyFiniteComplexMeasure :=
  ⟨localJordanDifference (Measure.dirac x) 0, localJordanDifference 0 0⟩

lemma pointMixer_control (x : ℝ) : (pointMixer x).variationControl = Measure.dirac x := by
  change ((Measure.dirac x - 0) + (0 - Measure.dirac x)) + ((0 - 0) + (0 - 0)) = _
  simp

lemma pointMixer_moment (x a : ℝ) : mixingExponentialMoment a (pointMixer x) < ∞ := by
  refine lt_of_le_of_lt (lintegral_mono' (LocallyFiniteComplexMeasure.totalVariation_le_control _)
    le_rfl) ?_
  rw [pointMixer_control, lintegral_dirac]
  exact ENNReal.ofReal_lt_top

lemma zeta_leakage_ratio_pos {a : ℝ} (ha : 1 / 2 < a) :
    0 < (riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re := by
  have hs : 1 < a + 1 / 2 := by linarith
  rw [show (2 * a + 1 : ℝ) = 2 * (a + 1 / 2) by ring, zeta_ratio_re hs]
  exact inv_pos.mpr (tsum_abs_moebius_rpow_pos hs)

/-- Non-vacuity of leakage: the actual mixture of δ₋₁ has strictly positive weighted
variation inside the gap (0,1), at least the explicit zeta-ratio bound. -/
theorem expected_point_mixer_leakage_positive (a : ℝ) (ha : 1 / 2 < a) :
    ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ENNReal.ofReal (Real.exp a) ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture (pointMixer (-1)) a ha.le (pointMixer_moment (-1) a)).rePart.totalVariation ∧
    0 < ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture (pointMixer (-1)) a ha.le (pointMixer_moment (-1) a)).rePart.totalVariation := by
  have hL := (weighted_gap_leakage.1 (pointMixer (-1)) a ha (pointMixer_moment (-1) a)).1
  have hσ : ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂(pointMixer (-1)).rePart.totalVariation =
      ENNReal.ofReal (Real.exp a) := by
    change ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t))
      ∂((Measure.dirac (-1) - 0) + (0 - Measure.dirac (-1))) = _
    simp only [Measure.sub_zero, Measure.zero_sub, add_zero]
    classical
    rw [setLIntegral_dirac, if_pos (show (-1 : ℝ) ∈ Iio 0 by norm_num)]
    congr 2
    ring
  rw [hσ] at hL
  refine ⟨hL, lt_of_lt_of_le ?_ hL⟩
  exact ENNReal.mul_pos (by simpa using zeta_leakage_ratio_pos ha) (by simp [Real.exp_pos])

/-- The δ₀ mixer: its mixture is exactly the integer comb measure. -/
lemma pointMixer_zero_positive (a : ℝ) (ha : 1 / 2 ≤ a) (hm : mixingExponentialMoment a (pointMixer 0) < ∞) :
    (weightedDilationMixture (pointMixer 0) a ha hm).rePart.positive = dilatedCombMeasure 0 ∧
    (weightedDilationMixture (pointMixer 0) a ha hm).rePart.negative = 0 ∧
    (weightedDilationMixture (pointMixer 0) a ha hm).imPart.positive = 0 ∧
    (weightedDilationMixture (pointMixer 0) a ha hm).imPart.negative = 0 := by
  have h0 : positiveDilationMixture (Measure.dirac (0 : ℝ) - 0) = dilatedCombMeasure 0 := by
    ext s hs
    rw [Measure.sub_zero, positiveDilationMixture_apply _ s hs, lintegral_dirac]
  have hz : positiveDilationMixture ((0 : Measure ℝ) - Measure.dirac 0) = 0 := by
    rw [Measure.zero_sub, positiveDilationMixture_zero]
  have hz' : positiveDilationMixture ((0 : Measure ℝ) - 0) = 0 := by
    rw [Measure.sub_zero, positiveDilationMixture_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change positiveDilationMixture (Measure.dirac 0 - 0) -
      positiveDilationMixture (0 - Measure.dirac 0) = _
    rw [h0, hz, Measure.sub_zero]
  · change positiveDilationMixture (0 - Measure.dirac 0) -
      positiveDilationMixture (Measure.dirac 0 - 0) = _
    rw [hz, Measure.zero_sub]
  · change positiveDilationMixture (0 - 0) - positiveDilationMixture (0 - 0) = _
    rw [hz', Measure.sub_self]
  · change positiveDilationMixture (0 - 0) - positiveDilationMixture (0 - 0) = _
    rw [hz', Measure.sub_self]

/-- Non-vacuity of the sharp-gap hypotheses: the δ₀ mixture has the exact punctured
gap, and the sharp-gap theorem then returns c = 1 and the integer comb. -/
theorem expected_point_mixer_gap (a : ℝ) (ha : 1 / 2 < a) :
    (weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).variationControl
        (Ioo (-1) 1 \ {0}) = 0 ∧
    (pointMixer 0).integral (fun _ => 1) = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := pointMixer_zero_positive a ha.le (pointMixer_moment 0 a)
  refine ⟨?_, ?_⟩
  · change (((weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).rePart.positive +
        (weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).rePart.negative) +
      ((weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).imPart.positive +
        (weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).imPart.negative))
        (Ioo (-1) 1 \ {0}) = 0
    rw [h1, h2, h3, h4]
    simpa using dilatedCombMeasure_punctured_gap 0
  · unfold LocallyFiniteComplexMeasure.integral
    change ((∫ _x, (1 : ℂ) ∂(Measure.dirac (0 : ℝ) - 0)) - (∫ _x, (1 : ℂ) ∂(0 - Measure.dirac 0))) +
      Complex.I * ((∫ _x, (1 : ℂ) ∂((0 : Measure ℝ) - 0)) - (∫ _x, (1 : ℂ) ∂((0 : Measure ℝ) - 0))) = 1
    simp

/-- The δ₀ mixture is the integer Dirac comb as a tempered distribution. -/
lemma pointMixer_zero_distribution (a : ℝ) (ha : 1 / 2 < a) :
    (weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (pointMixer 0) a ha.le (pointMixer_moment 0 a)) =
      dilatedCombDistribution 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := pointMixer_zero_positive a ha.le (pointMixer_moment 0 a)
  ext f
  rw [LocallyFiniteComplexMeasure.distributionOfLinearGrowth_apply, dilatedCombDistribution,
    LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
  unfold LocallyFiniteComplexMeasure.integral
  rw [h1, h2, h3, h4]
  simp [dilatedCombJordan, localJordanDifference]

/-- Full non-vacuity of the sharp-gap root: the actual δ₀ mixture satisfies both
hypotheses (canonical self-duality is Poisson summation, the gap is exact), and
the root applies to it. -/
theorem expected_point_mixer_sharp_gap_instance (a : ℝ) (ha : 1 / 2 < a) :
    𝓕 ((weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (pointMixer 0) a ha.le (pointMixer_moment 0 a))) =
      (weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (pointMixer 0) a ha.le (pointMixer_moment 0 a)) ∧
    (pointMixer 0).variationControl ({0}ᶜ) = 0 ∧
    (weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (pointMixer 0) a ha.le (pointMixer_moment 0 a)) =
      dilatedCombDistribution 0 := by
  have hD := pointMixer_zero_distribution a ha
  have hself : 𝓕 ((weightedDilationMixture (pointMixer 0) a ha.le
        (pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (pointMixer 0) a ha.le (pointMixer_moment 0 a))) =
      (weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (pointMixer 0) a ha.le (pointMixer_moment 0 a)) := by
    rw [hD]
    simpa using (dilated_comb_fourier 0).2.2
  obtain ⟨hgap, hc⟩ := expected_point_mixer_gap a ha
  obtain ⟨-, h1, h2, -, -⟩ :=
    weighted_mixture_sharp_gap (pointMixer 0) a ha (pointMixer_moment 0 a) hself hgap
  refine ⟨hself, h1, ?_⟩
  rw [h2, hc, one_smul]

/-- Falsification check: leakage needs the restriction to negative logarithmic
support. Integrated over all t, the δ₀ mixer has positive left side while its
actual mixture carries no variation in the gap (0,1). -/
theorem expected_leakage_needs_negative_support (a : ℝ) (ha : 1 / 2 < a) :
    ¬ (ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t)) ∂(pointMixer 0).rePart.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).rePart.totalVariation) := by
  obtain ⟨h1, h2, -, -⟩ := pointMixer_zero_positive a ha.le (pointMixer_moment 0 a)
  have hR : ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
      ∂(weightedDilationMixture (pointMixer 0) a ha.le (pointMixer_moment 0 a)).rePart.totalVariation = 0 := by
    refine setLIntegral_measure_zero _ _ ?_
    rw [LocallyFiniteSignedMeasure.totalVariation, h1, h2, add_zero]
    refine measure_mono_null (fun x hx => ?_) (dilatedCombMeasure_punctured_gap 0)
    rw [Real.exp_zero]
    exact ⟨⟨by linarith [hx.1], hx.2⟩, fun h => (ne_of_gt hx.1) h⟩
  have hL : ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t)) ∂(pointMixer 0).rePart.totalVariation = 1 := by
    change ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t))
      ∂((Measure.dirac (0 : ℝ) - 0) + (0 - Measure.dirac 0)) = 1
    simp
  rw [hR, hL, mul_one, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, not_le]
  exact zeta_leakage_ratio_pos ha

/-- The density form of leakage and the endpoint witness, restated. -/
theorem expected_density_leakage :
    (∀ (h : ℝ → ℂ) (H b : ℝ), 1 / 2 < b → Continuous h → (∀ t, h (-t) = h t) →
      (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      ENNReal.ofReal ((riemannZeta ((2 * b + 1 : ℝ) : ℂ) / riemannZeta ((b + 1 / 2 : ℝ) : ℂ)).re) *
          (⨆ t ∈ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (b * t) * ‖h t‖)) ≤
        ⨆ x ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (1 / 2 - b) * ‖mixtureDensity h x‖)) ∧
    (∀ b : ℝ, 1 / 2 < b → ∃ h : ℝ → ℂ, Continuous h ∧ (∀ t, h (-t) = h t) ∧
      (∀ t, ‖h t‖ ≤ 1 * Real.exp (-b * |t|)) ∧
      ∫⁻ t, ENNReal.ofReal (Real.exp (b * |t|) * ‖h t‖) = ∞) :=
  ⟨weighted_gap_leakage.2.1, weighted_gap_leakage.2.2.2⟩

end OPICAWeightedInverseIndependent
#print axioms Zeta23.OPICAFollowup.weighted_mobius_inverse
#print axioms Zeta23.OPICAFollowup.weighted_mixture_sharp_gap
#print axioms Zeta23.OPICAFollowup.weighted_gap_leakage
#print axioms OPICAWeightedInverseIndependent.audit_integerLogComb
#print axioms OPICAWeightedInverseIndependent.expected_moebius_lattice_identity
#print axioms OPICAWeightedInverseIndependent.expected_weighted_mobius_inverse_real
#print axioms OPICAWeightedInverseIndependent.expected_weighted_mixture_sharp_gap
#print axioms OPICAWeightedInverseIndependent.expected_weighted_gap_leakage_real
#print axioms OPICAWeightedInverseIndependent.expected_point_mixer_leakage_positive
#print axioms OPICAWeightedInverseIndependent.expected_point_mixer_gap
#print axioms OPICAWeightedInverseIndependent.expected_point_mixer_sharp_gap_instance
#print axioms OPICAWeightedInverseIndependent.expected_density_leakage
#print axioms OPICAWeightedInverseIndependent.expected_leakage_needs_negative_support
