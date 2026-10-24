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

end Zeta23.OPICAFollowup
