import Zeta23.OPICAFollowup.DilatedComb
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Actual noncompact mixing foundation. No primary WeightedMixing root is
claimed until the locally finite measure, absolute transport, and physical
origin law have all been proved. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped ENNReal Topology FourierTransform SchwartzMap
open Zeta23.OPICA
namespace Zeta23.OPICAFollowup

/-- The positive-axis logarithmic inversion needs the true x^(-1/2)
weight, not the unweighted log pushforward. This is its physical test weight,
defined as zero off the positive axis. It does not construct a measure. -/
def positiveLogWeight (x : ℝ) : ℝ :=
  if 0 < x then (Real.sqrt x)⁻¹ else 0

private theorem weighted_sqrt_exp_half (t : ℝ) :
    Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  have hsplit : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, Real.sqrt_mul_self (Real.exp_pos _).le]

/-- The exact Jacobian normalization behind the future positiveLogMeasure. -/
theorem positiveLogWeight_exp (t : ℝ) :
    positiveLogWeight (Real.exp t) = Real.exp (-t / 2) := by
  simp only [positiveLogWeight, if_pos (Real.exp_pos t), weighted_sqrt_exp_half]
  rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]

/-- Real logarithmic pullback of a complex test, before constructing the
locally finite weighted pushforward and proving absolute Möbius Fubini. -/
def weightedPositiveLogTest (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (positiveLogWeight x : ℂ) * f (Real.log x)

/-- Pullback evaluated on an actual positive dilation parameter. -/
theorem weightedPositiveLogTest_exp (f : ℝ → ℂ) (t : ℝ) :
    weightedPositiveLogTest f (Real.exp t) =
      (Real.exp (-t / 2) : ℂ) * f t := by
  simp only [weightedPositiveLogTest, positiveLogWeight_exp, Real.log_exp]

def weightedVariation (a : ℝ) (sigma : LocallyFiniteComplexMeasure) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (-a*t)) ∂sigma.totalVariation

def mixingExponentialMoment (a : ℝ) (sigma : LocallyFiniteComplexMeasure) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (a*|t|)) ∂sigma.totalVariation

lemma LocallyFiniteComplexMeasure.variationControl_le_twice
    (sigma : LocallyFiniteComplexMeasure) :
    sigma.variationControl≤sigma.totalVariation+sigma.totalVariation := by
  apply Measure.le_iff.mpr
  intro s hs
  have hmono : Monotone localMeasureInterval := by
    intro n m hnm
    apply Icc_subset_Icc
    · exact neg_le_neg (by exact_mod_cast hnm)
    · exact_mod_cast hnm
  calc
    sigma.variationControl s =
        sigma.variationControl.restrict (⋃ n : ℕ, localMeasureInterval n) s := by
      rw [localMeasureInterval_cover,Measure.restrict_univ]
    _ = ⨆ n : ℕ, sigma.variationControl.restrict (localMeasureInterval n) s :=
      Measure.restrict_iUnion_apply_eq_iSup hmono.directed_le hs
    _ ≤ (sigma.totalVariation+sigma.totalVariation) s := by
      apply iSup_le
      intro n
      have h := sigma.variationControl_restrict_le_two (localMeasureInterval n) isCompact_Icc
      exact (h s).trans ((add_le_add Measure.restrict_le_self Measure.restrict_le_self) s)

def mixtureLatticePoint (z : ℝ×ℤ) : ℝ := Real.exp z.1*(z.2:ℝ)

lemma mixtureLatticePoint_measurable : Measurable mixtureLatticePoint :=
  (Real.measurable_exp.comp measurable_fst).mul
    ((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp measurable_snd)

def mixtureAmplitude (z : ℝ×ℤ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (z.1/2))

lemma mixtureAmplitude_measurable : Measurable mixtureAmplitude := by
  unfold mixtureAmplitude
  fun_prop

def positiveDilationMixture (mu : Measure ℝ) : Measure ℝ :=
  Measure.map mixtureLatticePoint ((mu.prod (Measure.count : Measure ℤ)).withDensity mixtureAmplitude)

lemma mixtureLatticePoint_origin :
    mixtureLatticePoint ⁻¹' ({0} : Set ℝ) = (univ : Set ℝ) ×ˢ ({0} : Set ℤ) := by
  ext z
  simp [mixtureLatticePoint,Real.exp_ne_zero]

lemma positiveDilationMixture_origin (mu : Measure ℝ) [SFinite mu] :
    positiveDilationMixture mu ({0} : Set ℝ) =
      ∫⁻ t, ENNReal.ofReal (Real.exp (t/2)) ∂mu := by
  rw [positiveDilationMixture,Measure.map_apply mixtureLatticePoint_measurable (measurableSet_singleton 0),
    withDensity_apply _ (mixtureLatticePoint_measurable (measurableSet_singleton 0)),
    mixtureLatticePoint_origin,setLIntegral_prod _ mixtureAmplitude_measurable.aemeasurable]
  simp [mixtureAmplitude]

lemma positiveDilationMixture_apply (mu : Measure ℝ) [SFinite mu]
    (s : Set ℝ) (hs : MeasurableSet s) :
    positiveDilationMixture mu s = ∫⁻ t, dilatedCombMeasure t s ∂mu := by
  have hpre := mixtureLatticePoint_measurable hs
  rw [positiveDilationMixture,Measure.map_apply mixtureLatticePoint_measurable hs,
    withDensity_apply _ hpre,←lintegral_indicator hpre,
    lintegral_prod _ (mixtureAmplitude_measurable.indicator hpre).aemeasurable]
  apply lintegral_congr
  intro t
  have hsection : MeasurableSet ((scaledLatticePoint t) ⁻¹' s) :=
    scaledLatticePoint_measurable t hs
  have heq : (fun n : ℤ => (mixtureLatticePoint ⁻¹' s).indicator mixtureAmplitude (t,n)) =
      ((scaledLatticePoint t) ⁻¹' s).indicator
        (fun _ : ℤ => ENNReal.ofReal (Real.exp (t/2))) := by rfl
  rw [heq,lintegral_indicator hsection]
  simp only [lintegral_const,Measure.restrict_apply_univ,dilatedCombMeasure,
    Measure.smul_apply,smul_eq_mul,scaledLatticeMeasure,
    Measure.map_apply (scaledLatticePoint_measurable t) hs]

def positiveMixingMoment (a : ℝ) (mu : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (a*|t|)) ∂mu

lemma positiveDilationMixture_mass_bound (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (R : ℝ) (hR : 0≤R) :
    positiveDilationMixture mu (Icc (-R) R) ≤
      ENNReal.ofReal (3+2*R)*positiveMixingMoment a mu := by
  rw [positiveDilationMixture_apply mu _ measurableSet_Icc]
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (3+2*R)*ENNReal.ofReal (Real.exp (a*|t|)) ∂mu := by
      apply lintegral_mono
      intro t
      apply (dilated_comb_fourier t).1 R hR |>.trans
      dsimp only
      rw [←ENNReal.ofReal_mul (by positivity : 0≤3+2*R)]
      apply ENNReal.ofReal_le_ofReal
      have he₁ : Real.exp (t/2)≤Real.exp (a*|t|) := by
        apply Real.exp_le_exp.mpr
        nlinarith [le_abs_self t,abs_nonneg t,mul_nonneg (sub_nonneg.mpr ha) (abs_nonneg t)]
      have he₂ : Real.exp (-t/2)≤Real.exp (a*|t|) := by
        apply Real.exp_le_exp.mpr
        nlinarith [neg_le_abs t,abs_nonneg t,mul_nonneg (sub_nonneg.mpr ha) (abs_nonneg t)]
      have heq : Real.exp (t/2)*Real.exp (-t)=Real.exp (-t/2) := by
        rw [←Real.exp_add]
        congr 1
        ring
      calc
        _ = 3*Real.exp (t/2)+2*R*(Real.exp (t/2)*Real.exp (-t)) := by ring
        _ = 3*Real.exp (t/2)+2*R*Real.exp (-t/2) := by rw [heq]
        _ ≤ 3*Real.exp (a*|t|)+2*R*Real.exp (a*|t|) := by gcongr
        _ = _ := by ring
    _ = _ := lintegral_const_mul _ (by fun_prop)

theorem positiveDilationMixture_locallyFinite (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞) :
    IsLocallyFiniteMeasure (positiveDilationMixture mu) where
  finiteAtNhds x := by
    let R := |x|+1
    refine ⟨Ioo (-R) R,Ioo_mem_nhds (by dsimp [R]; linarith [neg_le_abs x])
      (by dsimp [R]; linarith [le_abs_self x]),?_⟩
    apply (measure_mono Ioo_subset_Icc_self).trans_lt
    exact (positiveDilationMixture_mass_bound mu a ha R (by dsimp [R]; positivity)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm)

theorem positiveDilationMixture_linearGrowth (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞) :
    LinearMassGrowth (positiveDilationMixture mu) := by
  refine ⟨5*(positiveMixingMoment a mu).toReal,by positivity,fun R hR => ?_⟩
  have hb := positiveDilationMixture_mass_bound mu a ha R hR
  have ht : ENNReal.ofReal (3+2*R)*positiveMixingMoment a mu≠∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.ne
  have hr := ENNReal.toReal_mono ht hb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤3+2*R)] at hr
  change (positiveDilationMixture mu (Icc (-R) R)).toReal≤_
  nlinarith [ENNReal.toReal_nonneg (a := positiveMixingMoment a mu)]

lemma positiveDilationMixture_schwartz_integrable (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞)
    (f : SchwartzMap ℝ ℂ) : Integrable f (positiveDilationMixture mu) := by
  have := positiveDilationMixture_locallyFinite mu a ha hm
  have := hasTemperateGrowth_of_linear_growth _ (positiveDilationMixture_linearGrowth mu a ha hm)
  exact f.integrable

lemma positiveDilationMixture_product_integrable (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞)
    (f : SchwartzMap ℝ ℂ) :
    Integrable (fun z : ℝ×ℤ => (Real.exp (z.1/2):ℂ)*f (mixtureLatticePoint z))
      (mu.prod (Measure.count : Measure ℤ)) := by
  have hf := positiveDilationMixture_schwartz_integrable mu a ha hm f
  have hp : Integrable (fun z => f (mixtureLatticePoint z))
      ((mu.prod (Measure.count : Measure ℤ)).withDensity mixtureAmplitude) :=
    (integrable_map_measure f.continuous.aestronglyMeasurable
      mixtureLatticePoint_measurable.aemeasurable).mp hf
  have hw := (integrable_withDensity_iff_integrable_smul' mixtureAmplitude_measurable
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))).mp hp
  apply hw.congr
  filter_upwards [] with z
  change (ENNReal.ofReal (Real.exp (z.1/2))).toReal • f (mixtureLatticePoint z) = _
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,RCLike.real_smul_eq_coe_mul]
  rfl

lemma mixture_count_integral (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    (∫ n : ℤ, (Real.exp (t/2):ℂ)*f (mixtureLatticePoint (t,n)) ∂Measure.count) =
      dilatedCombDistribution t f := by
  have hc : Integrable (fun n : ℤ => f (scaledLatticePoint t n)) Measure.count := by
    apply (integrable_map_measure f.continuous.aestronglyMeasurable
      (scaledLatticePoint_measurable t).aemeasurable).mp
    exact scaledLatticeMeasure_integrable_schwartz t f
  rw [dilatedCombDistribution_apply,integral_const_mul]
  congr 1
  change (∫ n : ℤ, f (scaledLatticePoint t n) ∂Measure.count) = _
  rw [integral_countable hc]
  simp only [count_real_singleton,one_smul,scaledLatticePoint]

lemma positiveDilationMixture_parameter_pairing_integrable (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞)
    (f : SchwartzMap ℝ ℂ) :
    Integrable (fun t => dilatedCombDistribution t f) mu := by
  have hp := (positiveDilationMixture_product_integrable mu a ha hm f).integral_prod_left
  exact hp.congr (Filter.Eventually.of_forall (fun t => mixture_count_integral t f))

lemma positiveDilationMixture_integral (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞)
    (f : SchwartzMap ℝ ℂ) :
    (∫ x, f x ∂positiveDilationMixture mu) = ∫ t, dilatedCombDistribution t f ∂mu := by
  rw [positiveDilationMixture,integral_map mixtureLatticePoint_measurable.aemeasurable
    f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul mixtureAmplitude_measurable
      (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  simp only [mixtureAmplitude,ENNReal.toReal_ofReal (Real.exp_nonneg _),
    RCLike.real_smul_eq_coe_mul]
  trans ∫ t, ∫ n : ℤ, (Real.exp (t/2):ℂ)*f (mixtureLatticePoint (t,n)) ∂Measure.count ∂mu
  · exact integral_prod _ (positiveDilationMixture_product_integrable mu a ha hm f)
  · exact integral_congr_ae (Filter.Eventually.of_forall (fun t => mixture_count_integral t f))

-- Append inside namespace Zeta23.OPICAFollowup after the checked positive foundation.

lemma mixing_part_moment_lt_top (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (hm : mixingExponentialMoment a sigma<∞) (mu : Measure ℝ)
    (hmu : mu≤sigma.variationControl) : positiveMixingMoment a mu<∞ := by
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (a*|t|))
        ∂(sigma.totalVariation+sigma.totalVariation) :=
      lintegral_mono' (hmu.trans sigma.variationControl_le_twice) le_rfl
    _ = mixingExponentialMoment a sigma+mixingExponentialMoment a sigma := by
      rw [lintegral_add_measure]
      rfl
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hm,hm⟩

lemma weightedJordanPositive_le_totalVariation (mu : LocallyFiniteSignedMeasure) :
    mu.positive≤mu.totalVariation := by
  intro s
  rw [LocallyFiniteSignedMeasure.totalVariation,Measure.add_apply]
  exact le_add_of_nonneg_right zero_le

lemma weightedJordanNegative_le_totalVariation (mu : LocallyFiniteSignedMeasure) :
    mu.negative≤mu.totalVariation := by
  intro s
  rw [LocallyFiniteSignedMeasure.totalVariation,Measure.add_apply]
  exact le_add_of_nonneg_left zero_le

lemma weightedReal_le_control (sigma : LocallyFiniteComplexMeasure) :
    sigma.rePart.totalVariation≤sigma.variationControl := by
  intro s
  rw [LocallyFiniteComplexMeasure.variationControl,Measure.add_apply]
  exact le_add_of_nonneg_right zero_le

lemma weightedImaginary_le_control (sigma : LocallyFiniteComplexMeasure) :
    sigma.imPart.totalVariation≤sigma.variationControl := by
  intro s
  rw [LocallyFiniteComplexMeasure.variationControl,Measure.add_apply]
  exact le_add_of_nonneg_left zero_le

def mixingCoordinate (sigma : LocallyFiniteComplexMeasure) (i : Fin 4) : Measure ℝ :=
  if i=0 then sigma.rePart.positive else if i=1 then sigma.rePart.negative else
    if i=2 then sigma.imPart.positive else sigma.imPart.negative

instance mixingCoordinate_locallyFinite (sigma : LocallyFiniteComplexMeasure) (i : Fin 4) :
    IsLocallyFiniteMeasure (mixingCoordinate sigma i) := by
  fin_cases i <;> dsimp [mixingCoordinate] <;> infer_instance

lemma mixingCoordinate_le_control (sigma : LocallyFiniteComplexMeasure) (i : Fin 4) :
    mixingCoordinate sigma i≤sigma.variationControl := by
  fin_cases i
  · simpa [mixingCoordinate] using
      (weightedJordanPositive_le_totalVariation sigma.rePart).trans (weightedReal_le_control sigma)
  · simpa [mixingCoordinate] using
      (weightedJordanNegative_le_totalVariation sigma.rePart).trans (weightedReal_le_control sigma)
  · simpa [mixingCoordinate] using
      (weightedJordanPositive_le_totalVariation sigma.imPart).trans (weightedImaginary_le_control sigma)
  · simpa [mixingCoordinate] using
      (weightedJordanNegative_le_totalVariation sigma.imPart).trans (weightedImaginary_le_control sigma)

lemma mixingCoordinate_moment (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (hm : mixingExponentialMoment a sigma<∞) (i : Fin 4) :
    positiveMixingMoment a (mixingCoordinate sigma i)<∞ :=
  mixing_part_moment_lt_top sigma a hm _ (mixingCoordinate_le_control sigma i)

def weightedDilationMixture (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2≤a) (hm : mixingExponentialMoment a sigma<∞) : LocallyFiniteComplexMeasure := by
  let m (i : Fin 4) := positiveDilationMixture (mixingCoordinate sigma i)
  letI : IsLocallyFiniteMeasure (m 0) :=
    positiveDilationMixture_locallyFinite _ a ha (mixingCoordinate_moment sigma a hm 0)
  letI : IsLocallyFiniteMeasure (m 1) :=
    positiveDilationMixture_locallyFinite _ a ha (mixingCoordinate_moment sigma a hm 1)
  letI : IsLocallyFiniteMeasure (m 2) :=
    positiveDilationMixture_locallyFinite _ a ha (mixingCoordinate_moment sigma a hm 2)
  letI : IsLocallyFiniteMeasure (m 3) :=
    positiveDilationMixture_locallyFinite _ a ha (mixingCoordinate_moment sigma a hm 3)
  exact ⟨localJordanDifference (m 0) (m 1),localJordanDifference (m 2) (m 3)⟩

lemma weightedPositiveGrowth_add (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu]
    (hmu : LinearMassGrowth mu) (hnu : LinearMassGrowth nu) : LinearMassGrowth (mu+nu) := by
  obtain ⟨C,hC,hBC⟩ := hmu
  obtain ⟨D,hD,hBD⟩ := hnu
  refine ⟨C+D,add_nonneg hC hD,fun R hR => ?_⟩
  rw [measureReal_def,Measure.add_apply,
    ENNReal.toReal_add (isCompact_Icc.measure_lt_top.ne) (isCompact_Icc.measure_lt_top.ne)]
  have hC' := hBC R hR
  have hD' := hBD R hR
  change (mu (Icc (-R) R)).toReal≤_ at hC'
  change (nu (Icc (-R) R)).toReal≤_ at hD'
  nlinarith

lemma weightedDilationMixture_growth (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2≤a) (hm : mixingExponentialMoment a sigma<∞) :
    (weightedDilationMixture sigma a ha hm).HasLinearGrowth := by
  let m (i : Fin 4) := positiveDilationMixture (mixingCoordinate sigma i)
  have hfinite (i : Fin 4) : IsLocallyFiniteMeasure (m i) :=
    positiveDilationMixture_locallyFinite _ a ha (mixingCoordinate_moment sigma a hm i)
  have hgrowth (i : Fin 4) : LinearMassGrowth (m i) :=
    positiveDilationMixture_linearGrowth _ a ha (mixingCoordinate_moment sigma a hm i)
  have := hfinite 0
  have := hfinite 1
  have := hfinite 2
  have := hfinite 3
  have hre : (localJordanDifference (m 0) (m 1)).HasLinearGrowth :=
    (weightedPositiveGrowth_add _ _ (hgrowth 0) (hgrowth 1)).mono
      (localJordanDifference_variation_le _ _)
  have him : (localJordanDifference (m 2) (m 3)).HasLinearGrowth :=
    (weightedPositiveGrowth_add _ _ (hgrowth 2) (hgrowth 3)).mono
      (localJordanDifference_variation_le _ _)
  exact weightedPositiveGrowth_add _ _ hre him

lemma weightedDilationMixture_pairing (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2≤a) (hm : mixingExponentialMoment a sigma<∞) (f : SchwartzMap ℝ ℂ) :
    (weightedDilationMixture sigma a ha hm).integral f =
      sigma.integral (fun t => dilatedCombDistribution t f) := by
  let m (i : Fin 4) := positiveDilationMixture (mixingCoordinate sigma i)
  have hfinite (i : Fin 4) : IsLocallyFiniteMeasure (m i) :=
    positiveDilationMixture_locallyFinite _ a ha (mixingCoordinate_moment sigma a hm i)
  have := hfinite 0
  have := hfinite 1
  have := hfinite 2
  have := hfinite 3
  have hint (i : Fin 4) : Integrable f (m i) :=
    positiveDilationMixture_schwartz_integrable _ a ha (mixingCoordinate_moment sigma a hm i) f
  have hpair (i : Fin 4) : (∫ x, f x ∂m i)=
      ∫ t, dilatedCombDistribution t f ∂mixingCoordinate sigma i :=
    positiveDilationMixture_integral _ a ha (mixingCoordinate_moment sigma a hm i) f
  change (((∫ x, f x ∂(localJordanDifference (m 0) (m 1)).positive)-
    (∫ x, f x ∂(localJordanDifference (m 0) (m 1)).negative))+
    I*((∫ x, f x ∂(localJordanDifference (m 2) (m 3)).positive)-
    (∫ x, f x ∂(localJordanDifference (m 2) (m 3)).negative))) = _
  rw [localJordanDifference_integral _ _ _ (hint 0) (hint 1),
    localJordanDifference_integral _ _ _ (hint 2) (hint 3),hpair 0,hpair 1,hpair 2,hpair 3]
  rfl

-- Append inside namespace after genuine complex assembly.
def reflectedMixingPositiveMeasure (mu : Measure ℝ) : Measure ℝ :=
  Measure.map (fun t : ℝ => -t) mu

instance reflectedMixingPositiveMeasure_sFinite (mu : Measure ℝ) [SFinite mu] :
    SFinite (reflectedMixingPositiveMeasure mu) := by
  unfold reflectedMixingPositiveMeasure
  infer_instance

instance reflectedMixingPositiveMeasure_locallyFinite (mu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] : IsLocallyFiniteMeasure (reflectedMixingPositiveMeasure mu) where
  finiteAtNhds x := by
    let R := |x|+1
    refine ⟨Ioo (-R) R,Ioo_mem_nhds (by dsimp [R]; linarith [neg_le_abs x])
      (by dsimp [R]; linarith [le_abs_self x]),?_⟩
    rw [reflectedMixingPositiveMeasure,Measure.map_apply measurable_neg measurableSet_Ioo]
    have hpre : (fun t : ℝ => -t) ⁻¹' Ioo (-R) R=Ioo (-R) R := by
      ext t
      simp only [mem_preimage,mem_Ioo]
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
    rw [hpre]
    exact (measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top

def reflectedMixingJordan (mu : LocallyFiniteSignedMeasure) : LocallyFiniteSignedMeasure where
  positive := reflectedMixingPositiveMeasure mu.positive
  negative := reflectedMixingPositiveMeasure mu.negative
  positive_locallyFinite := inferInstance
  negative_locallyFinite := inferInstance
  mutuallySingular := (Homeomorph.neg ℝ).measurableEmbedding.mutuallySingular_map mu.mutuallySingular

def reflectedMixingMeasure (sigma : LocallyFiniteComplexMeasure) : LocallyFiniteComplexMeasure :=
  ⟨reflectedMixingJordan sigma.rePart,reflectedMixingJordan sigma.imPart⟩

lemma positiveMixingMoment_reflect (mu : Measure ℝ) (a : ℝ) :
    positiveMixingMoment a (reflectedMixingPositiveMeasure mu)=positiveMixingMoment a mu := by
  rw [positiveMixingMoment,reflectedMixingPositiveMeasure,
    lintegral_map' (by fun_prop) measurable_neg.aemeasurable]
  simp only [abs_neg,positiveMixingMoment]

lemma reflectedMixingMeasure_coordinate (sigma : LocallyFiniteComplexMeasure) (i : Fin 4) :
    mixingCoordinate (reflectedMixingMeasure sigma) i=
      reflectedMixingPositiveMeasure (mixingCoordinate sigma i) := by
  fin_cases i <;> rfl

lemma mixingExponentialMoment_reflect_lt_top (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (hm : mixingExponentialMoment a sigma<∞) :
    mixingExponentialMoment a (reflectedMixingMeasure sigma)<∞ := by
  have hcoord (i : Fin 4) :
      positiveMixingMoment a (mixingCoordinate (reflectedMixingMeasure sigma) i)<∞ := by
    rw [reflectedMixingMeasure_coordinate,positiveMixingMoment_reflect]
    exact mixingCoordinate_moment sigma a hm i
  have hsum : (∫⁻ t, ENNReal.ofReal (Real.exp (a*|t|))
      ∂(reflectedMixingMeasure sigma).variationControl)<∞ := by
    change (∫⁻ t, ENNReal.ofReal (Real.exp (a*|t|))
      ∂((mixingCoordinate (reflectedMixingMeasure sigma) 0+
          mixingCoordinate (reflectedMixingMeasure sigma) 1)+
        (mixingCoordinate (reflectedMixingMeasure sigma) 2+
          mixingCoordinate (reflectedMixingMeasure sigma) 3)))<∞
    rw [lintegral_add_measure,lintegral_add_measure,lintegral_add_measure]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hcoord 0,hcoord 1⟩,
      ENNReal.add_lt_top.mpr ⟨hcoord 2,hcoord 3⟩⟩
  exact (lintegral_mono' (reflectedMixingMeasure sigma).totalVariation_le_control le_rfl).trans_lt hsum

lemma positiveDilationMixture_fourier_pairing (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞) (f : SchwartzMap ℝ ℂ) :
    (∫ x, (𝓕 f) x ∂positiveDilationMixture mu)=
      ∫ x, f x ∂positiveDilationMixture (reflectedMixingPositiveMeasure mu) := by
  have hmr : positiveMixingMoment a (reflectedMixingPositiveMeasure mu)<∞ := by
    rwa [positiveMixingMoment_reflect]
  rw [positiveDilationMixture_integral mu a ha hm (𝓕 f),
    positiveDilationMixture_integral _ a ha hmr f]
  have hint := positiveDilationMixture_parameter_pairing_integrable _ a ha hmr f
  rw [reflectedMixingPositiveMeasure,
    integral_map measurable_neg.aemeasurable hint.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with t
  exact congrArg (fun T : TemperedDistribution ℝ ℂ => T f) (dilated_comb_fourier t).2.2

lemma reflectedMixingMeasure_integral (sigma : LocallyFiniteComplexMeasure) (g : ℝ → ℂ)
    (hg : ∀ i : Fin 4, Integrable g
      (reflectedMixingPositiveMeasure (mixingCoordinate sigma i))) :
    (reflectedMixingMeasure sigma).integral g = sigma.integral (fun t => g (-t)) := by
  have hmap (i : Fin 4) :
      (∫ t, g t ∂reflectedMixingPositiveMeasure (mixingCoordinate sigma i)) =
        ∫ t, g (-t) ∂mixingCoordinate sigma i :=
    integral_map measurable_neg.aemeasurable (hg i).aestronglyMeasurable
  change ((∫ t, g t ∂reflectedMixingPositiveMeasure (mixingCoordinate sigma 0)) -
      (∫ t, g t ∂reflectedMixingPositiveMeasure (mixingCoordinate sigma 1))) +
    I * ((∫ t, g t ∂reflectedMixingPositiveMeasure (mixingCoordinate sigma 2)) -
      (∫ t, g t ∂reflectedMixingPositiveMeasure (mixingCoordinate sigma 3))) = _
  rw [hmap 0,hmap 1,hmap 2,hmap 3]
  rfl

lemma weightedDilationMixture_fourier_pairing (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2≤a) (hm : mixingExponentialMoment a sigma<∞) (f : SchwartzMap ℝ ℂ) :
    (weightedDilationMixture sigma a ha hm).integral (𝓕 f : SchwartzMap ℝ ℂ) =
      (weightedDilationMixture (reflectedMixingMeasure sigma) a ha
        (mixingExponentialMoment_reflect_lt_top sigma a hm)).integral f := by
  rw [weightedDilationMixture_pairing,weightedDilationMixture_pairing]
  have hint (i : Fin 4) : Integrable (fun t => dilatedCombDistribution t f)
      (reflectedMixingPositiveMeasure (mixingCoordinate sigma i)) := by
    apply positiveDilationMixture_parameter_pairing_integrable _ a ha _ f
    rw [positiveMixingMoment_reflect]
    exact mixingCoordinate_moment sigma a hm i
  rw [reflectedMixingMeasure_integral sigma _ hint]
  have heq (t : ℝ) : dilatedCombDistribution t (𝓕 f)=dilatedCombDistribution (-t) f :=
    congrArg (fun T : TemperedDistribution ℝ ℂ => T f) (dilated_comb_fourier t).2.2
  exact congrArg sigma.integral (funext heq)

lemma weightedDilationMixture_fourier (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2≤a) (hm : mixingExponentialMoment a sigma<∞) :
    𝓕 ((weightedDilationMixture sigma a ha hm).distributionOfLinearGrowth
      (weightedDilationMixture_growth sigma a ha hm)) =
      (weightedDilationMixture (reflectedMixingMeasure sigma) a ha
        (mixingExponentialMoment_reflect_lt_top sigma a hm)).distributionOfLinearGrowth
          (weightedDilationMixture_growth _ _ _ _) := by
  ext1 f
  exact weightedDilationMixture_fourier_pairing sigma a ha hm f

lemma positiveDilationMixture_origin_integrable (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞) :
    Integrable (fun t : ℝ => Real.exp (t/2)) mu := by
  have := positiveDilationMixture_locallyFinite mu a ha hm
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall (fun t => (Real.exp_pos _).le))).mp
  rw [←positiveDilationMixture_origin mu]
  exact (isCompact_singleton.measure_lt_top (μ := positiveDilationMixture mu)).ne

lemma positiveDilationMixture_origin_real (mu : Measure ℝ) [SFinite mu]
    (a : ℝ) (ha : 1/2≤a) (hm : positiveMixingMoment a mu<∞) :
    (positiveDilationMixture mu).real ({0} : Set ℝ)=∫ t, Real.exp (t/2) ∂mu := by
  rw [measureReal_def,positiveDilationMixture_origin,
    ←ofReal_integral_eq_lintegral_ofReal (positiveDilationMixture_origin_integrable mu a ha hm)
      (Eventually.of_forall (fun t => (Real.exp_pos _).le)),ENNReal.toReal_ofReal]
  exact integral_nonneg (fun t => (Real.exp_pos _).le)

lemma weightedLocalJordanDifference_atom (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu] :
    localSignedCompactRestriction (localJordanDifference mu nu) ({0} : Set ℝ)
      isCompact_singleton ({0} : Set ℝ)=mu.real ({0} : Set ℝ)-nu.real ({0} : Set ℝ) := by
  rw [localJordanDifference_compactRestriction]
  have : IsFiniteMeasure (mu.restrict ({0} : Set ℝ)) :=
    isFiniteMeasure_restrict.mpr isCompact_singleton.measure_lt_top.ne
  have : IsFiniteMeasure (nu.restrict ({0} : Set ℝ)) :=
    isFiniteMeasure_restrict.mpr isCompact_singleton.measure_lt_top.ne
  rw [_root_.sub_apply,Measure.toSignedMeasure_apply_measurable (measurableSet_singleton 0),
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton 0)]
  simp [measureReal_def]

lemma weightedDilationMixture_origin (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2≤a) (hm : mixingExponentialMoment a sigma<∞) :
    (weightedDilationMixture sigma a ha hm).compactRestriction ({0} : Set ℝ)
      isCompact_singleton ({0} : Set ℝ) = sigma.integral (fun t => (Real.exp (t/2) : ℂ)) := by
  let m (i : Fin 4) := positiveDilationMixture (mixingCoordinate sigma i)
  have hfinite (i : Fin 4) : IsLocallyFiniteMeasure (m i) :=
    positiveDilationMixture_locallyFinite _ a ha (mixingCoordinate_moment sigma a hm i)
  have := hfinite 0
  have := hfinite 1
  have := hfinite 2
  have := hfinite 3
  have hatom (i : Fin 4) : (m i).real ({0} : Set ℝ)=
      ∫ t, Real.exp (t/2) ∂mixingCoordinate sigma i :=
    positiveDilationMixture_origin_real _ a ha (mixingCoordinate_moment sigma a hm i)
  have hcast (i : Fin 4) :
      (∫ t, (Real.exp (t/2) : ℂ) ∂mixingCoordinate sigma i) =
        Complex.ofReal (∫ t, Real.exp (t/2) ∂mixingCoordinate sigma i) := integral_ofReal
  change (localSignedCompactRestriction (localJordanDifference (m 0) (m 1)) _ _).toComplexMeasure
    (localSignedCompactRestriction (localJordanDifference (m 2) (m 3)) _ _) _ = _
  rw [SignedMeasure.toComplexMeasure_apply,
    weightedLocalJordanDifference_atom,weightedLocalJordanDifference_atom,
    hatom 0,hatom 1,hatom 2,hatom 3]
  change Complex.mk (_-_) (_-_) =
    (∫ t, (Real.exp (t/2) : ℂ) ∂mixingCoordinate sigma 0) -
      (∫ t, (Real.exp (t/2) : ℂ) ∂mixingCoordinate sigma 1) +
    I * ((∫ t, (Real.exp (t/2) : ℂ) ∂mixingCoordinate sigma 2) -
      (∫ t, (Real.exp (t/2) : ℂ) ∂mixingCoordinate sigma 3))
  rw [hcast 0,hcast 1,hcast 2,hcast 3]
  apply Complex.ext <;> simp

/-- Actual complex weighted mixing in the full noncompact exponential class.
The strict threshold of HT1 is retained even though the construction alone
admits the endpoint. No inverse or sharp-gap assertion is included here. -/
theorem weighted_mixture_exists_fourier (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2<a) (hm : mixingExponentialMoment a sigma<∞) :
    ∃ (nu : LocallyFiniteComplexMeasure) (hg : nu.HasLinearGrowth),
      nu=weightedDilationMixture sigma a ha.le hm ∧
      (∀ f : SchwartzMap ℝ ℂ, nu.integral f=
        sigma.integral (fun t => dilatedCombDistribution t f)) ∧
      𝓕 (nu.distributionOfLinearGrowth hg)=
        (weightedDilationMixture (reflectedMixingMeasure sigma) a ha.le
          (mixingExponentialMoment_reflect_lt_top sigma a hm)).distributionOfLinearGrowth
            (weightedDilationMixture_growth _ _ _ _) ∧
      nu.compactRestriction ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ)=
        sigma.integral (fun t => (Real.exp (t/2) : ℂ)) ∧
      (∀ (f : SchwartzMap ℝ ℂ) (i : Fin 4),
        Integrable (fun z : ℝ × ℤ => (Real.exp (z.1/2) : ℂ)*f (mixtureLatticePoint z))
          ((mixingCoordinate sigma i).prod (Measure.count : Measure ℤ))) := by
  refine ⟨weightedDilationMixture sigma a ha.le hm,
    weightedDilationMixture_growth sigma a ha.le hm,rfl,?_,?_,?_,?_⟩
  · exact weightedDilationMixture_pairing sigma a ha.le hm
  · exact weightedDilationMixture_fourier sigma a ha.le hm
  · exact weightedDilationMixture_origin sigma a ha.le hm
  · intro f i
    exact positiveDilationMixture_product_integrable _ a ha.le
      (mixingCoordinate_moment sigma a hm i) f

end Zeta23.OPICAFollowup
