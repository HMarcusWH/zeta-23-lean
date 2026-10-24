import Zeta23.OPICAFollowup.DilatedComb
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual noncompact mixing (R1-HT1): the locally finite weighted mixture with
its Fourier transport and origin law, the weighted Möbius inverse in the
positive lattice algebra, the noncompact sharp gap and the quantitative gap
leakage in measure form (with the genuine complex variations) and in
continuous-density supremum form, where the density r_h is identified with the
actual density of the mixture of h(t) dt on the positive axis. -/
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

/-- The logarithmic pullback vanishes on nonpositive arguments, retaining
the zero-origin atom separately in the later measure construction. -/
theorem weightedPositiveLogTest_nonpos (f : ℝ → ℂ) {x : ℝ}
    (hx : x ≤ 0) : weightedPositiveLogTest f x = 0 := by
  simp only [weightedPositiveLogTest, positiveLogWeight, if_neg (not_lt.mpr hx)]
  simp

/-- Every actual positive integer dilation has the required n^(-1/2) factor
after the x^(-1/2) logarithmic pullback.  This is a genuine finite pointwise
identity, not yet a Möbius measure inversion or a Fubini theorem. -/
theorem weightedPositiveLogTest_at_dilatedNat (f : ℝ → ℂ) (t : ℝ)
    (n : ℕ) (hn : 0 < n) :
    weightedPositiveLogTest f (Real.exp t * (n : ℝ)) =
      ((Real.exp (-t / 2) / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        f (t + Real.log (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hprod : 0 < Real.exp t * (n : ℝ) :=
    mul_pos (Real.exp_pos t) hnreal
  have hsqrt : Real.sqrt (Real.exp t * (n : ℝ)) =
      Real.exp (t / 2) * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (Real.exp_nonneg t), weighted_sqrt_exp_half]
  have hlog : Real.log (Real.exp t * (n : ℝ)) =
      t + Real.log (n : ℝ) := by
    rw [Real.log_mul (Real.exp_pos t).ne' hnreal.ne', Real.log_exp]
  have hweight : positiveLogWeight (Real.exp t * (n : ℝ)) =
      Real.exp (-t / 2) / Real.sqrt (n : ℝ) := by
    unfold positiveLogWeight
    rw [if_pos hprod, hsqrt, mul_inv_rev]
    rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]
    ring
  unfold weightedPositiveLogTest
  rw [hweight, hlog]

/-- Actual positive-axis weighted logarithmic pushforward. The restriction
eliminates the zero atom *before* taking logarithms. Every nonzero integer
lattice atom is weighted by x^(-1/2); neither an assumed inverse transform
nor a globally finite measure is part of this definition.

This is the positive-measure component of the eventual complex Jordan-coordinate
inversion. The complete complex Möbius identity remains OPEN. -/
def positiveLogMeasure (mu : Measure ℝ) : Measure ℝ :=
  Measure.map Real.log
    ((mu.restrict (Ioi (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (positiveLogWeight x)))

/-- The actual positive-axis logarithmic transport is additive for
arbitrary input measures, even if they have infinite global mass. This is the
measure-level linearity needed to assemble individual atoms into the integer
comb before the Möbius inverse is applied. -/
theorem positiveLogMeasure_add (mu nu : Measure ℝ) :
    positiveLogMeasure (mu + nu) =
      positiveLogMeasure mu + positiveLogMeasure nu := by
  unfold positiveLogMeasure
  rw [Measure.restrict_add, MeasureTheory.withDensity_add_measure]
  exact Measure.map_add _ _ Real.measurable_log

/-- The positive-axis weighted logarithmic pushforward commutes with
arbitrary nonnegative measure sums. This is the measure-level bridge from
finite integer atoms to the noncompact lattice, before complex Jordan
assembly and absolute Mobius Fubini. Neither a synthetic transform nor a
whole-line finite-output hypothesis is used. -/
theorem positiveLogMeasure_sum {ι : Type*} (mu : ι → Measure ℝ) :
    positiveLogMeasure (Measure.sum mu) =
      Measure.sum (fun i => positiveLogMeasure (mu i)) := by
  unfold positiveLogMeasure
  ext s hs
  rw [Measure.map_apply Real.measurable_log hs,
    Measure.restrict_sum mu measurableSet_Ioi,
    MeasureTheory.withDensity_sum,
    Measure.sum_apply _ (Real.measurable_log hs),
    Measure.sum_apply _ hs]
  simp_rw [Measure.map_apply Real.measurable_log hs]

/-- The canonical zero input has no positive logarithmic mass. -/
theorem positiveLogMeasure_zero : positiveLogMeasure (0 : Measure ℝ) = 0 := by
  simp [positiveLogMeasure, MeasureTheory.withDensity_zero_left]

theorem positiveLogMeasure_dirac (t : ℝ) :
    positiveLogMeasure (Measure.dirac (Real.exp t)) =
      ENNReal.ofReal (Real.exp (-t / 2)) • (Measure.dirac t) := by
  classical
  unfold positiveLogMeasure
  rw [MeasureTheory.restrict_dirac]
  simp only [Set.mem_Ioi, Real.exp_pos, ↓reduceIte]
  rw [MeasureTheory.dirac_withDensity, positiveLogWeight_exp, Measure.map_smul,
    Measure.map_dirac, Real.log_exp]

/-- Zero and negative atomic inputs disappear *before* logarithmic transport.
This is the origin firewall: the integer comb's 0 atom must be accounted for
separately rather than silently pushed to Real.log 0. -/
theorem positiveLogMeasure_dirac_nonpos {x : ℝ} (hx : x ≤ 0) :
    positiveLogMeasure (Measure.dirac x) = 0 := by
  classical
  unfold positiveLogMeasure
  rw [MeasureTheory.restrict_dirac]
  have hnot : x ∉ Ioi (0 : ℝ) := not_lt.mpr hx
  simp only [Set.mem_Ioi] at hnot
  simp [hnot]

/-- Dirac normalisation on every positive input, not only exponential inputs.
The compact logarithmic measure is weighted by the original inverse
square-root source rather than an artificially normalized mass. -/
theorem positiveLogMeasure_dirac_pos {x : ℝ} (hx : 0 < x) :
    positiveLogMeasure (Measure.dirac x) =
      ENNReal.ofReal (positiveLogWeight x) • (Measure.dirac (Real.log x)) := by
  classical
  unfold positiveLogMeasure
  rw [MeasureTheory.restrict_dirac]
  simp only [Set.mem_Ioi, hx, ↓reduceIte]
  rw [MeasureTheory.dirac_withDensity, Measure.map_smul, Measure.map_dirac]

/-- Exact logarithmic transport of one physical positive integer-lattice
atom. The n^(-1/2) factor comes from the same native weighted test as the
eventual Möbius convolution; n=0 is excluded by the proven origin firewall. -/
theorem positiveLogMeasure_dilatedNat_dirac (t : ℝ) (n : ℕ) (hn : 0 < n) :
    positiveLogMeasure (Measure.dirac (Real.exp t * (n : ℝ))) =
      ENNReal.ofReal (Real.exp (-t / 2) / Real.sqrt (n : ℝ)) •
        Measure.dirac (t + Real.log (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hprod : 0 < Real.exp t * (n : ℝ) :=
    mul_pos (Real.exp_pos t) hnreal
  have hw := weightedPositiveLogTest_at_dilatedNat (fun _ => (1 : ℂ)) t n hn
  have hweight : positiveLogWeight (Real.exp t * (n : ℝ)) =
      Real.exp (-t / 2) / Real.sqrt (n : ℝ) := by
    apply Complex.ofReal_injective
    simpa [weightedPositiveLogTest] using hw
  have hlog : Real.log (Real.exp t * (n : ℝ)) =
      t + Real.log (n : ℝ) := by
    rw [Real.log_mul (Real.exp_pos t).ne' hnreal.ne', Real.log_exp]
  rw [positiveLogMeasure_dirac_pos hprod, hweight, hlog]

/-- Genuine finite arithmetic superpositions commute with the
positive-axis weighted log transport. This is the finite precursor of the
counting-measure Fubini theorem, not a replacement for infinite inversion. -/
theorem positiveLogMeasure_finset_sum {ι : Type*} (s : Finset ι)
    (mu : ι → Measure ℝ) :
    positiveLogMeasure (∑ i ∈ s, mu i) =
      ∑ i ∈ s, positiveLogMeasure (mu i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, positiveLogMeasure_zero]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, positiveLogMeasure_add, ih]

/-- Physical finite integer atoms transport to the exact weighted logarithmic
lattice, with coefficient 1/sqrt(n) and a retained common time translation.
Every atom is genuinely positive and nonzero before taking logarithms. -/
theorem positiveLogMeasure_finite_integer_lattice
    (t : ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) :
    positiveLogMeasure
      (∑ n ∈ s, Measure.dirac (Real.exp t * (n : ℝ))) =
      ∑ n ∈ s,
        ENNReal.ofReal (Real.exp (-t / 2) / Real.sqrt (n : ℝ)) •
          Measure.dirac (t + Real.log (n : ℝ)) := by
  rw [positiveLogMeasure_finset_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  exact positiveLogMeasure_dilatedNat_dirac t n (hs n hn)

/-- The actual positive integer lattice, with n=0 explicitly excluded.
It is a noncompact counting measure, rather than a finite or caller-supplied
packet, so it can be consumed by the genuine logarithmic inversion lane. -/
def positiveIntegerLatticeInput (t : ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ =>
    Measure.dirac (Real.exp t * (((n + 1 : ℕ) : ℝ))))

/-- Exact all-integer log transport: every physical n >= 1 atom becomes
the correct shifted log atom, carrying n^(-1/2) and the source dilation.
This proof uses countable measure additivity; it neither assumes finite
total output mass nor invokes a nonabsolute Möbius rearrangement. -/
theorem positiveLogMeasure_integerLattice (t : ℝ) :
    positiveLogMeasure (positiveIntegerLatticeInput t) =
      Measure.sum (fun n : ℕ =>
        ENNReal.ofReal (Real.exp (-t / 2) /
          Real.sqrt (((n + 1 : ℕ) : ℝ))) •
          Measure.dirac (t + Real.log (((n + 1 : ℕ) : ℝ)))) := by
  unfold positiveIntegerLatticeInput
  rw [positiveLogMeasure_sum]
  congr 1
  funext n
  exact positiveLogMeasure_dilatedNat_dirac t (n + 1) (Nat.zero_lt_succ n)

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

/-! ### Discrete logarithmic lattice measures (the weighted measure algebra) -/

/-- The weight k^(-1/2) on positive integers, zero at k = 0. -/
def latticeWeight (k : ℕ) : ℝ≥0∞ :=
  if k = 0 then 0 else ENNReal.ofReal (Real.sqrt (k : ℝ))⁻¹

/-- The positive lattice measure Σ_k w(k) δ_(log k). -/
def latticeMeasure (w : ℕ → ℝ≥0∞) : Measure ℝ :=
  Measure.sum (fun k : ℕ => w k • Measure.dirac (Real.log k))

/-- N = Σ_(n ≥ 1) n^(-1/2) δ_(log n). -/
def integerLogComb : Measure ℝ := latticeMeasure latticeWeight

/-- M⁺ = Σ_(μ(n) = 1) n^(-1/2) δ_(log n). -/
def moebiusPlusComb : Measure ℝ :=
  latticeMeasure (fun k => if ArithmeticFunction.moebius k = 1 then latticeWeight k else 0)

/-- M⁻ = Σ_(μ(n) = -1) n^(-1/2) δ_(log n). -/
def moebiusMinusComb : Measure ℝ :=
  latticeMeasure (fun k => if ArithmeticFunction.moebius k = -1 then latticeWeight k else 0)

instance latticeMeasure_sFinite (w : ℕ → ℝ≥0∞) : SFinite (latticeMeasure w) := by
  unfold latticeMeasure
  infer_instance

instance integerLogComb_sFinite : SFinite integerLogComb := by
  unfold integerLogComb; infer_instance
instance moebiusPlusComb_sFinite : SFinite moebiusPlusComb := by
  unfold moebiusPlusComb; infer_instance
instance moebiusMinusComb_sFinite : SFinite moebiusMinusComb := by
  unfold moebiusMinusComb; infer_instance

theorem lintegral_latticeMeasure (w : ℕ → ℝ≥0∞) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂latticeMeasure w = ∑' k, w k * f (Real.log k) := by
  unfold latticeMeasure
  rw [lintegral_sum_measure]
  congr 1
  funext k
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem latticeMeasure_conv (w : ℕ → ℝ≥0∞) (ρ : Measure ℝ) [SFinite ρ] :
    latticeMeasure w ∗ ρ =
      Measure.sum (fun k : ℕ => w k • ρ.map (fun y => Real.log k + y)) := by
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  rw [Measure.lintegral_conv hf, lintegral_latticeMeasure, lintegral_sum_measure]
  congr 1
  funext k
  rw [lintegral_smul_measure, lintegral_map hf (by fun_prop), smul_eq_mul]

theorem latticeMeasure_conv_apply (w : ℕ → ℝ≥0∞) (ρ : Measure ℝ) [SFinite ρ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    (latticeMeasure w ∗ ρ) s = ∑' k, w k * ρ ((fun y => Real.log k + y) ⁻¹' s) := by
  rw [latticeMeasure_conv, Measure.sum_apply _ hs]
  congr 1
  funext k
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) hs, smul_eq_mul]

lemma latticeWeight_mul {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    latticeWeight i * latticeWeight j = latticeWeight (i * j) := by
  have hij : i * j ≠ 0 := mul_ne_zero hi hj
  simp only [latticeWeight, if_neg hi, if_neg hj, if_neg hij]
  rw [← ENNReal.ofReal_mul (by positivity), Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]

/-- Regrouping a positive double lattice sum by products (absolute Fubini for
positive coefficients). -/
theorem tsum_lattice_pairs (F : ℕ → ℕ → ℝ≥0∞) (hF : ∀ i j, i = 0 ∨ j = 0 → F i j = 0) :
    ∑' i, ∑' j, F i j = ∑' k : ℕ, ∑ p ∈ Nat.divisorsAntidiagonal k, F p.1 p.2 := by
  rw [← ENNReal.tsum_prod]
  -- restrict to positive pairs
  have hpos : ∑' p : ℕ × ℕ, F p.1 p.2 = ∑' p : ℕ+ × ℕ+, F p.1 p.2 := by
    let e : ℕ+ × ℕ+ → ℕ × ℕ := fun p => ((p.1 : ℕ), (p.2 : ℕ))
    have he : Function.Injective e := by
      intro p q h
      simp only [e, Prod.mk.injEq] at h
      exact Prod.ext (PNat.coe_injective h.1) (PNat.coe_injective h.2)
    refine (he.tsum_eq ?_).symm
    intro p hp
    rw [Function.mem_support] at hp
    have h1 : p.1 ≠ 0 := fun h => hp (hF _ _ (Or.inl h))
    have h2 : p.2 ≠ 0 := fun h => hp (hF _ _ (Or.inr h))
    exact ⟨(⟨p.1, Nat.pos_of_ne_zero h1⟩, ⟨p.2, Nat.pos_of_ne_zero h2⟩), rfl⟩
  rw [hpos, ← sigmaAntidiagonalEquivProd.tsum_eq, ENNReal.tsum_sigma']
  have hk0 : ∑' k : ℕ, ∑ p ∈ k.divisorsAntidiagonal, F p.1 p.2 =
      ∑' k : ℕ+, ∑ p ∈ (k : ℕ).divisorsAntidiagonal, F p.1 p.2 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ => ∑ p ∈ Nat.divisorsAntidiagonal k, F p.1 p.2),
      tsum_eq_zero_add' ENNReal.summable]
    simp
  rw [hk0]
  refine tsum_congr (fun n => ?_)
  rw [tsum_fintype, ← Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
    (fun p => F p.1 p.2), Finset.univ_eq_attach]
  rfl

theorem latticeMeasure_conv_latticeMeasure (v w : ℕ → ℝ≥0∞) (hv : v 0 = 0) (hw : w 0 = 0) :
    latticeMeasure v ∗ latticeMeasure w =
      latticeMeasure (fun k : ℕ => ∑ p ∈ Nat.divisorsAntidiagonal k, v p.1 * w p.2) := by
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  rw [Measure.lintegral_conv hf, lintegral_latticeMeasure, lintegral_latticeMeasure]
  simp_rw [lintegral_latticeMeasure, ← ENNReal.tsum_mul_left, Finset.sum_mul]
  rw [tsum_lattice_pairs (fun i j => v i * (w j * f (Real.log i + Real.log j)))]
  · refine tsum_congr (fun k => Finset.sum_congr rfl (fun p hp => ?_))
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    have h1 : p.1 ≠ 0 := left_ne_zero_of_mul (hp'.1 ▸ hp'.2 : p.1 * p.2 ≠ 0)
    have h2 : p.2 ≠ 0 := right_ne_zero_of_mul (hp'.1 ▸ hp'.2 : p.1 * p.2 ≠ 0)
    rw [← Real.log_mul (by exact_mod_cast h1) (by exact_mod_cast h2), ← Nat.cast_mul, hp'.1]
    ring
  · rintro i j (rfl | rfl)
    · simp [hv]
    · simp [hw]


/-! ### Möbius inversion in the positive lattice algebra -/

lemma moebius_divisor_sum (k : ℕ) :
    ∑ d ∈ k.divisors, ArithmeticFunction.moebius d = if k = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F k) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [h, ArithmeticFunction.one_apply]

lemma moebius_plus_minus_card {k : ℕ} (hk : k ≠ 1) :
    (k.divisors.filter (fun d => ArithmeticFunction.moebius d = 1)).card =
      (k.divisors.filter (fun d => ArithmeticFunction.moebius d = -1)).card := by
  have hsplit : ∀ d, ArithmeticFunction.moebius d =
      (if ArithmeticFunction.moebius d = 1 then 1 else 0) -
        (if ArithmeticFunction.moebius d = -1 then 1 else 0) := by
    intro d
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
  have h := moebius_divisor_sum k
  rw [if_neg hk, Finset.sum_congr rfl (fun d _ => hsplit d), Finset.sum_sub_distrib,
    Finset.sum_boole, Finset.sum_boole, sub_eq_zero] at h
  exact_mod_cast h

/-- Coefficient form of M⁺ ∗ N = δ₀ + M⁻ ∗ N. -/
lemma moebius_lattice_coefficients (k : ℕ) :
    ∑ p ∈ Nat.divisorsAntidiagonal k,
        (if ArithmeticFunction.moebius p.1 = 1 then latticeWeight p.1 else 0) * latticeWeight p.2 =
      (if k = 1 then 1 else 0) +
        ∑ p ∈ Nat.divisorsAntidiagonal k,
          (if ArithmeticFunction.moebius p.1 = -1 then latticeWeight p.1 else 0) *
            latticeWeight p.2 := by
  have hterm (c : ℤ) : ∀ p ∈ Nat.divisorsAntidiagonal k,
      (if ArithmeticFunction.moebius p.1 = c then latticeWeight p.1 else 0) * latticeWeight p.2 =
        (if ArithmeticFunction.moebius p.1 = c then 1 else 0) * latticeWeight k := by
    intro p hp
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    have h1 : p.1 ≠ 0 := left_ne_zero_of_mul (hp'.1 ▸ hp'.2 : p.1 * p.2 ≠ 0)
    have h2 : p.2 ≠ 0 := right_ne_zero_of_mul (hp'.1 ▸ hp'.2 : p.1 * p.2 ≠ 0)
    split_ifs
    · rw [one_mul, latticeWeight_mul h1 h2, hp'.1]
    · simp
  rw [Finset.sum_congr rfl (hterm 1), Finset.sum_congr rfl (hterm (-1)), ← Finset.sum_mul,
    ← Finset.sum_mul, Finset.sum_boole, Finset.sum_boole]
  have hcard (c : ℤ) : ((Nat.divisorsAntidiagonal k).filter
      (fun p => ArithmeticFunction.moebius p.1 = c)).card =
      (k.divisors.filter (fun d => ArithmeticFunction.moebius d = c)).card := by
    rw [← Nat.map_div_right_divisors, Finset.filter_map, Finset.card_map]
    rfl
  rw [hcard 1, hcard (-1)]
  by_cases hk : k = 1
  · subst hk
    simp [latticeWeight, Finset.filter_singleton]
  · rw [if_neg hk, zero_add, moebius_plus_minus_card hk]

theorem moebiusPlus_conv_integerLogComb :
    moebiusPlusComb ∗ integerLogComb = Measure.dirac 0 + moebiusMinusComb ∗ integerLogComb := by
  have hp0 : (if ArithmeticFunction.moebius 0 = 1 then latticeWeight 0 else 0) = 0 := by simp
  have hm0 : (if ArithmeticFunction.moebius 0 = -1 then latticeWeight 0 else 0) = 0 := by simp
  have hl0 : latticeWeight 0 = 0 := by simp [latticeWeight]
  unfold moebiusPlusComb moebiusMinusComb integerLogComb
  rw [latticeMeasure_conv_latticeMeasure _ _ hp0 hl0, latticeMeasure_conv_latticeMeasure _ _ hm0 hl0]
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  rw [lintegral_add_measure, lintegral_latticeMeasure, lintegral_latticeMeasure, lintegral_dirac]
  simp_rw [moebius_lattice_coefficients, add_mul]
  rw [ENNReal.tsum_add]
  congr 1
  rw [tsum_eq_single 1 (fun k hk => by simp [hk])]
  simp

/-- Positive form of σ = M_μ ∗ (N ∗ σ): M⁺∗N∗ρ = ρ + M⁻∗N∗ρ, by associativity of
the genuine product-measure convolution (absolute Fubini). -/
theorem moebius_inverse_positive (ρ : Measure ℝ) [SFinite ρ] :
    moebiusPlusComb ∗ (integerLogComb ∗ ρ) = ρ + moebiusMinusComb ∗ (integerLogComb ∗ ρ) := by
  rw [← Measure.conv_assoc, ← Measure.conv_assoc, moebiusPlus_conv_integerLogComb,
    Measure.add_conv, Measure.dirac_zero_conv]

/-! ### Weighted norms -/

/-- The weighted variation norm ‖τ‖_(-a) = ∫ e^(-a y) dτ of a positive measure. -/
def weightedLogNorm (a : ℝ) (ρ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (Real.exp (-a * y)) ∂ρ

/-- The weighted norm is exactly multiplicative for positive convolution. -/
theorem weightedLogNorm_conv (a : ℝ) (μ ρ : Measure ℝ) [SFinite ρ] :
    weightedLogNorm a (μ ∗ ρ) = weightedLogNorm a μ * weightedLogNorm a ρ := by
  unfold weightedLogNorm
  rw [Measure.lintegral_conv (by fun_prop)]
  have h (x y : ℝ) : ENNReal.ofReal (Real.exp (-a * (x + y))) =
      ENNReal.ofReal (Real.exp (-a * x)) * ENNReal.ofReal (Real.exp (-a * y)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  simp_rw [h]
  simp_rw [lintegral_const_mul _ (by fun_prop : Measurable fun y : ℝ =>
    ENNReal.ofReal (Real.exp (-a * y)))]
  rw [lintegral_mul_const _ (by fun_prop)]

theorem weightedLogNorm_latticeMeasure (a : ℝ) (w : ℕ → ℝ≥0∞) :
    weightedLogNorm a (latticeMeasure w) =
      ∑' k, w k * ENNReal.ofReal (Real.exp (-a * Real.log k)) := by
  unfold weightedLogNorm
  rw [lintegral_latticeMeasure]

lemma latticeWeight_exp {a : ℝ} (ha : 0 < a + 1 / 2) (k : ℕ) :
    latticeWeight k * ENNReal.ofReal (Real.exp (-a * Real.log k)) =
      ENNReal.ofReal ((k : ℝ) ^ (-(a + 1 / 2))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
    simp [latticeWeight]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [latticeWeight, if_neg hk.ne']
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hk'.le, mul_comm (-a), ← Real.rpow_def_of_pos hk',
      ← Real.rpow_add hk']
    ring_nf

/-! ### Norm values: ‖N‖ = ζ(s) and ‖M_μ‖ = ζ(s)/ζ(2s), s = a + 1/2 -/

lemma real_tsum_rpow_eq_zeta {s : ℝ} (hs : 1 < s) :
    ((∑' n : ℕ, (n : ℝ) ^ (-s) : ℝ) : ℂ) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hs), Complex.ofReal_tsum]
  refine tsum_congr (fun n => ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv, one_div,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

lemma summable_nat_rpow_neg {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
  Real.summable_nat_rpow.mpr (by linarith)

theorem weightedLogNorm_integerLogComb {a : ℝ} (ha : 1 / 2 < a) :
    weightedLogNorm a integerLogComb = ENNReal.ofReal (∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2))) := by
  unfold integerLogComb
  rw [weightedLogNorm_latticeMeasure]
  simp_rw [latticeWeight_exp (by linarith : 0 < a + 1 / 2)]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (summable_nat_rpow_neg (by linarith))]

/-- The norm of the Möbius lattice |M_μ| = M⁺ + M⁻. -/
theorem weightedLogNorm_moebiusComb {a : ℝ} (ha : 1 / 2 < a) :
    weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) =
      ENNReal.ofReal (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) := by
  have hpos : 0 < a + 1 / 2 := by linarith
  unfold weightedLogNorm moebiusPlusComb moebiusMinusComb
  rw [lintegral_add_measure]
  change weightedLogNorm a _ + weightedLogNorm a _ = _
  rw [weightedLogNorm_latticeMeasure, weightedLogNorm_latticeMeasure, ← ENNReal.tsum_add]
  have hsum : Summable (fun n : ℕ =>
      (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) := by
    refine (summable_nat_rpow_neg (by linarith : 1 < a + 1 / 2)).of_nonneg_of_le
      (fun n => by positivity) (fun n => ?_)
    have h := ArithmeticFunction.abs_moebius_le_one (n := n)
    have h' : (|ArithmeticFunction.moebius n| : ℝ) ≤ 1 := by exact_mod_cast h
    calc _ ≤ 1 * (n : ℝ) ^ (-(a + 1 / 2)) := mul_le_mul_of_nonneg_right h' (by positivity)
      _ = _ := one_mul _
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
  refine tsum_congr (fun n => ?_)
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h
  · simp [h]
  · simp only [h, if_true, show (1 : ℤ) ≠ -1 by decide, if_false, zero_mul, add_zero,
      latticeWeight_exp hpos]
    norm_num
  · simp only [h, show (-1 : ℤ) ≠ 1 by decide, if_true, if_false, zero_mul, zero_add,
      latticeWeight_exp hpos]
    norm_num

/-- Σ |μ(n)| n^(-s) = ζ(s)/ζ(2s) for real s > 1, via Euler products. -/
theorem tsum_abs_moebius_rpow {s : ℝ} (hs : 1 < s) :
    ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) =
      riemannZeta s / riemannZeta (2 * s) := by
  set f : ℕ → ℂ := fun n => ((|ArithmeticFunction.moebius n| : ℝ) : ℂ) * (n : ℂ) ^ (-(s : ℂ))
    with hfdef
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (by linarith : s ≠ 0)
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hfdef]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    simp only [Int.cast_mul, abs_mul, Complex.ofReal_mul]
    ring
  have hnorm (n : ℕ) : ‖f n‖ = (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-s) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hfdef]
    · simp only [hfdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      rw [Complex.norm_natCast_cpow_of_pos hn]
      simp
  have hsumR : Summable (fun n : ℕ => (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-s)) := by
    refine (summable_nat_rpow_neg hs).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    have h' : (|ArithmeticFunction.moebius n| : ℝ) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc _ ≤ 1 * (n : ℝ) ^ (-s) := mul_le_mul_of_nonneg_right h' (by positivity)
      _ = _ := one_mul _
  have hsum : Summable (‖f ·‖) := by simpa only [hnorm] using hsumR
  have hcast : (∑' n, f n) =
      ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    simp only [hfdef]
    rw [Complex.ofReal_mul, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  -- local Euler factors
  have hfactor (p : Nat.Primes) : ∑' e, f ((p : ℕ) ^ e) = 1 + (p : ℂ) ^ (-(s : ℂ)) := by
    have hp := p.prop
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one,
        hf1]
      simp only [hfdef, ArithmeticFunction.moebius_apply_prime hp]
      simp
    · intro e he
      have he2 : 2 ≤ e := by simp at he; omega
      simp only [hfdef]
      rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
      simp
  have hE := EulerProduct.eulerProduct_hasProd hf1 hmul hsum hf0
  simp_rw [hfactor] at hE
  have h2s : 1 < ((2 * s : ℝ) : ℂ).re := by simp; linarith
  have hZ2 := riemannZeta_eulerProduct_hasProd h2s
  have hZ := riemannZeta_eulerProduct_hasProd (s := (s : ℂ)) (by simpa using hs)
  have hprod := hE.mul hZ2
  have hpt (p : Nat.Primes) : (1 + (p : ℂ) ^ (-(s : ℂ))) * (1 - (p : ℂ) ^ (-((2 * s : ℝ) : ℂ)))⁻¹ =
      (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹ := by
    set x : ℂ := (p : ℂ) ^ (-(s : ℂ)) with hx
    have hx2 : (p : ℂ) ^ (-((2 * s : ℝ) : ℂ)) = x ^ 2 := by
      rw [hx, ← Complex.cpow_nat_mul]
      push_cast
      ring_nf
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
    have hxn : ‖x‖ < 1 := by
      rw [hx, Complex.norm_natCast_cpow_of_pos p.prop.pos]
      simp only [Complex.neg_re, Complex.ofReal_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have h1 : 1 - x ≠ 0 := by
      intro h
      have : x = 1 := by linear_combination -h
      rw [this, norm_one] at hxn
      exact lt_irrefl _ hxn
    have h2 : 1 + x ≠ 0 := by
      intro h
      have : x = -1 := by linear_combination h
      rw [this, norm_neg, norm_one] at hxn
      exact lt_irrefl _ hxn
    rw [hx2, show (1 : ℂ) - x ^ 2 = (1 - x) * (1 + x) by ring, mul_inv]
    field_simp
  simp_rw [hpt] at hprod
  have hunique := hprod.unique hZ
  have hz2 : riemannZeta ((2 * s : ℝ) : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2s
  rw [← hcast, eq_div_iff (by simpa using hz2)]
  have : ((2 * s : ℝ) : ℂ) = 2 * (s : ℂ) := by push_cast; ring
  rw [this] at hunique
  exact hunique

/-! ### η = N ∗ σ for the actual mixture -/

lemma positiveLogWeight_dilated (t : ℝ) {n : ℕ} (hn : 0 < n) :
    positiveLogWeight (Real.exp t * n) = Real.exp (-t / 2) / Real.sqrt n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : 0 < Real.exp t * (n : ℝ) := mul_pos (Real.exp_pos t) hnreal
  have hsqrt : Real.sqrt (Real.exp t * (n : ℝ)) = Real.exp (t / 2) * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (Real.exp_nonneg t)]
    congr 1
    rw [show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) by rw [← Real.exp_add]; ring_nf,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  unfold positiveLogWeight
  rw [if_pos hprod, hsqrt, mul_inv_rev, show -t / 2 = -(t / 2) by ring, Real.exp_neg]
  ring

instance positiveLogMeasure_sFinite (ρ : Measure ℝ) [SFinite ρ] :
    SFinite (positiveLogMeasure ρ) := by
  unfold positiveLogMeasure
  infer_instance

lemma lintegral_positiveLogMeasure (ρ : Measure ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂positiveLogMeasure ρ =
      ∫⁻ x, (Ioi (0 : ℝ)).indicator
        (fun x => ENNReal.ofReal (positiveLogWeight x) * f (Real.log x)) x ∂ρ := by
  have hw : Measurable (fun x : ℝ => ENNReal.ofReal (positiveLogWeight x)) := by
    unfold positiveLogWeight
    exact ENNReal.measurable_ofReal.comp
      (Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const)
  have h := lintegral_withDensity_eq_lintegral_mul (ρ.restrict (Ioi 0)) hw
    (hf.comp Real.measurable_log)
  simp only [Function.comp_def] at h
  unfold positiveLogMeasure
  rw [lintegral_map hf Real.measurable_log, h, lintegral_indicator measurableSet_Ioi]
  rfl

/-- The paper's (HT1.4): the weighted logarithmic pushforward of the actual
positive-axis mixture is the genuine convolution N ∗ μ. -/
theorem positiveLogMeasure_positiveDilationMixture (μ : Measure ℝ) [SFinite μ] :
    positiveLogMeasure (positiveDilationMixture μ) = integerLogComb ∗ μ := by
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  have hg : Measurable ((Ioi (0 : ℝ)).indicator
      (fun x => ENNReal.ofReal (positiveLogWeight x) * f (Real.log x))) := by
    refine Measurable.indicator ?_ measurableSet_Ioi
    unfold positiveLogWeight
    exact (ENNReal.measurable_ofReal.comp
      (Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const)).mul
      (hf.comp Real.measurable_log)
  set G := (Ioi (0 : ℝ)).indicator
      (fun x => ENNReal.ofReal (positiveLogWeight x) * f (Real.log x)) with hG
  have hGL : Measurable (fun z : ℝ × ℤ => G (mixtureLatticePoint z)) :=
    hg.comp mixtureLatticePoint_measurable
  rw [lintegral_positiveLogMeasure _ hf, positiveDilationMixture,
    lintegral_map hg mixtureLatticePoint_measurable,
    lintegral_withDensity_eq_lintegral_mul _ mixtureAmplitude_measurable hGL,
    lintegral_prod _ ((mixtureAmplitude_measurable.mul hGL).aemeasurable)]
  rw [Measure.lintegral_conv hf]
  unfold integerLogComb
  rw [lintegral_latticeMeasure]
  simp_rw [lintegral_count, Pi.mul_apply]
  have hterm (t : ℝ) : (∑' n : ℤ, mixtureAmplitude (t, n) * G (mixtureLatticePoint (t, n))) =
      ∑' k : ℕ, latticeWeight k * f (Real.log k + t) := by
    let F : ℤ → ℝ≥0∞ := fun n => mixtureAmplitude (t, n) * G (mixtureLatticePoint (t, n))
    change ∑' n, F n = _
    have hsupp : Function.support F ⊆ Set.range (fun k : ℕ => (k : ℤ)) := by
      intro n hn
      by_contra hcon
      apply hn
      have hn0 : n ≤ 0 := by
        by_contra h
        exact hcon ⟨n.toNat, Int.toNat_of_nonneg (by omega)⟩
      simp only [F, hG, mixtureLatticePoint]
      rw [Set.indicator_of_notMem, mul_zero]
      simp only [Set.mem_Ioi, not_lt]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos t).le (by exact_mod_cast hn0)
    rw [← (Nat.cast_injective (R := ℤ)).tsum_eq hsupp]
    refine tsum_congr (fun k => ?_)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [F, hG, latticeWeight, mixtureLatticePoint]
    · have hpos : 0 < Real.exp t * (k : ℝ) := mul_pos (Real.exp_pos t) (by exact_mod_cast hk)
      simp only [F, hG, mixtureLatticePoint, Int.cast_natCast]
      rw [Set.indicator_of_mem (show Real.exp t * (k : ℝ) ∈ Ioi 0 from hpos),
        positiveLogWeight_dilated t hk, Real.log_mul (Real.exp_pos t).ne'
          (by exact_mod_cast hk.ne'), Real.log_exp, add_comm t, ← mul_assoc]
      congr 1
      simp only [mixtureAmplitude, latticeWeight, if_neg hk.ne']
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [mul_div, ← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero, one_div]
  simp_rw [hterm]
  rw [lintegral_tsum]
  · refine tsum_congr (fun k => ?_)
    rw [lintegral_const_mul]
    exact hf.comp (by fun_prop)
  · intro k
    exact ((hf.comp (by fun_prop : Measurable fun x : ℝ => Real.log k + x)).const_mul _).aemeasurable

/-! ### Weighted finiteness and cancellation -/

lemma weightedLogNorm_le_moment (a : ℝ) (ha : 0 ≤ a) (ρ : Measure ℝ) :
    weightedLogNorm a ρ ≤ positiveMixingMoment a ρ := by
  unfold weightedLogNorm positiveMixingMoment
  refine lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  nlinarith [neg_abs_le t, abs_nonneg t]

lemma measure_Icc_lt_top_of_weightedLogNorm {a : ℝ} (ha : 0 ≤ a) {ρ : Measure ℝ}
    (hρ : weightedLogNorm a ρ < ∞) (R : ℝ) : ρ (Icc (-R) R) < ∞ := by
  have hle : ENNReal.ofReal (Real.exp (-a * R)) * ρ (Icc (-R) R) ≤ weightedLogNorm a ρ := by
    calc ENNReal.ofReal (Real.exp (-a * R)) * ρ (Icc (-R) R) =
        ∫⁻ y in Icc (-R) R, ENNReal.ofReal (Real.exp (-a * R)) ∂ρ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in Icc (-R) R, ENNReal.ofReal (Real.exp (-a * y)) ∂ρ := by
          refine setLIntegral_mono (by fun_prop) (fun y hy => ?_)
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [hy.2]))
      _ ≤ weightedLogNorm a ρ := setLIntegral_le_lintegral _ _
  have hpos : ENNReal.ofReal (Real.exp (-a * R)) ≠ 0 := by
    simp [Real.exp_pos]
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, ENNReal.mul_top hpos, top_le_iff] at hle
  exact (hρ.trans_le hle.ge).ne rfl

/-- Cancellation of a measure that is finite on every compact interval. -/
lemma measure_add_right_cancel_of_Icc {A B X : Measure ℝ}
    (hX : ∀ R : ℝ, X (Icc (-R) R) < ∞) (h : A + X = B + X) : A = B := by
  apply Measure.ext_of_iUnion_eq_univ localMeasureInterval_cover
  intro n
  ext s hs
  have hs' := congrArg (fun μ : Measure ℝ => μ (s ∩ localMeasureInterval n)) h
  simp only [Measure.add_apply] at hs'
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  have hfin : X (s ∩ localMeasureInterval n) ≠ ∞ :=
    (measure_mono inter_subset_right).trans_lt (hX n) |>.ne
  exact (ENNReal.add_left_inj hfin).mp hs'

lemma positiveLogMeasure_mono {μ ν : Measure ℝ} (h : μ ≤ ν) :
    positiveLogMeasure μ ≤ positiveLogMeasure ν := by
  refine Measure.le_iff.mpr (fun s hs => ?_)
  have hf : Measurable (s.indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs,
    lintegral_positiveLogMeasure _ hf, lintegral_positiveLogMeasure _ hf]
  exact lintegral_mono' h le_rfl

lemma weightedLogNorm_mono (a : ℝ) {μ ν : Measure ℝ} (h : μ ≤ ν) :
    weightedLogNorm a μ ≤ weightedLogNorm a ν :=
  lintegral_mono' h le_rfl

lemma weightedLogNorm_add (a : ℝ) (μ ν : Measure ℝ) :
    weightedLogNorm a (μ + ν) = weightedLogNorm a μ + weightedLogNorm a ν := by
  unfold weightedLogNorm
  rw [lintegral_add_measure]

lemma weightedLogNorm_integerLogComb_lt_top {a : ℝ} (ha : 1 / 2 < a) :
    weightedLogNorm a integerLogComb < ∞ := by
  rw [weightedLogNorm_integerLogComb ha]
  exact ENNReal.ofReal_lt_top

lemma weightedLogNorm_moebiusComb_lt_top {a : ℝ} (ha : 1 / 2 < a) :
    weightedLogNorm a moebiusPlusComb < ∞ ∧ weightedLogNorm a moebiusMinusComb < ∞ := by
  have h := weightedLogNorm_moebiusComb ha
  rw [weightedLogNorm_add] at h
  have ht : weightedLogNorm a moebiusPlusComb + weightedLogNorm a moebiusMinusComb < ∞ := by
    rw [h]; exact ENNReal.ofReal_lt_top
  exact ⟨lt_of_le_of_lt le_self_add ht, lt_of_le_of_lt le_add_self ht⟩

/-! ### The complex inverse for the actual mixture -/

/-- Real-part form of σ = M_μ ∗ η from η = N ∗ σ (positive form, no subtraction). -/
theorem moebius_inverse_jordan {a : ℝ} (ha : 1 / 2 < a)
    (σp σn ηp ηn : Measure ℝ) [SFinite σp] [SFinite σn] [SFinite ηp] [SFinite ηn]
    (hσp : weightedLogNorm a σp < ∞) (hσn : weightedLogNorm a σn < ∞)
    (hη : ηp + integerLogComb ∗ σn = ηn + integerLogComb ∗ σp) :
    σp + (moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) =
      σn + (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn) := by
  have ha0 : 0 ≤ a := by linarith
  have h1 := congrArg (fun μ => moebiusPlusComb ∗ μ) hη
  have h2 := congrArg (fun μ => moebiusMinusComb ∗ μ) hη
  simp only [Measure.conv_add, moebius_inverse_positive] at h1 h2
  set X := moebiusMinusComb ∗ (integerLogComb ∗ σn) + moebiusMinusComb ∗ (integerLogComb ∗ σp)
    with hXdef
  have hXnorm : weightedLogNorm a X < ∞ := by
    rw [hXdef, weightedLogNorm_add, weightedLogNorm_conv, weightedLogNorm_conv,
      weightedLogNorm_conv, weightedLogNorm_conv]
    have hM := (weightedLogNorm_moebiusComb_lt_top ha).2
    have hN := weightedLogNorm_integerLogComb_lt_top ha
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hM (ENNReal.mul_lt_top hN hσn),
      ENNReal.mul_lt_top hM (ENNReal.mul_lt_top hN hσp)⟩
  refine measure_add_right_cancel_of_Icc (X := X)
    (fun R => measure_Icc_lt_top_of_weightedLogNorm ha0 hXnorm R) ?_
  calc σp + (moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) + X =
      (moebiusPlusComb ∗ ηn + (σp + moebiusMinusComb ∗ (integerLogComb ∗ σp))) +
        (moebiusMinusComb ∗ ηp + moebiusMinusComb ∗ (integerLogComb ∗ σn)) := by
        rw [hXdef]; abel
    _ = (moebiusPlusComb ∗ ηp + (σn + moebiusMinusComb ∗ (integerLogComb ∗ σn))) +
        (moebiusMinusComb ∗ ηn + moebiusMinusComb ∗ (integerLogComb ∗ σp)) := by
        rw [← h1, h2]
    _ = σn + (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn) + X := by
        rw [hXdef]; abel

lemma mixingCoordinate_zero (σ : LocallyFiniteComplexMeasure) :
    mixingCoordinate σ 0 = σ.rePart.positive := rfl
lemma mixingCoordinate_one (σ : LocallyFiniteComplexMeasure) :
    mixingCoordinate σ 1 = σ.rePart.negative := rfl
lemma mixingCoordinate_two (σ : LocallyFiniteComplexMeasure) :
    mixingCoordinate σ 2 = σ.imPart.positive := rfl
lemma mixingCoordinate_three (σ : LocallyFiniteComplexMeasure) :
    mixingCoordinate σ 3 = σ.imPart.negative := rfl

lemma weightedLogNorm_mixingCoordinate {σ : LocallyFiniteComplexMeasure} {a : ℝ}
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞) (i : Fin 4) :
    weightedLogNorm a (mixingCoordinate σ i) < ∞ :=
  (weightedLogNorm_le_moment a (by linarith) _).trans_lt (mixingCoordinate_moment σ a hm i)

/-- η = N ∗ σ for one Jordan coordinate pair of the actual mixture. -/
lemma mixture_log_jordan (μp μn : Measure ℝ) [IsLocallyFiniteMeasure (positiveDilationMixture μp)]
    [IsLocallyFiniteMeasure (positiveDilationMixture μn)] [SFinite μp] [SFinite μn] :
    positiveLogMeasure (localJordanDifference (positiveDilationMixture μp)
        (positiveDilationMixture μn)).positive + integerLogComb ∗ μn =
      positiveLogMeasure (localJordanDifference (positiveDilationMixture μp)
        (positiveDilationMixture μn)).negative + integerLogComb ∗ μp := by
  have h := congrArg positiveLogMeasure
    (locallyFiniteMeasure_jordan_cross_sum (positiveDilationMixture μp) (positiveDilationMixture μn))
  rw [positiveLogMeasure_add, positiveLogMeasure_add, positiveLogMeasure_positiveDilationMixture,
    positiveLogMeasure_positiveDilationMixture] at h
  exact h

lemma mixture_log_part_norm {a : ℝ} (ha : 1 / 2 < a) (μp μn : Measure ℝ)
    [IsLocallyFiniteMeasure (positiveDilationMixture μp)]
    [IsLocallyFiniteMeasure (positiveDilationMixture μn)] [SFinite μp]
    (hp : weightedLogNorm a μp < ∞) :
    weightedLogNorm a (positiveLogMeasure (localJordanDifference (positiveDilationMixture μp)
        (positiveDilationMixture μn)).positive) < ∞ := by
  refine (weightedLogNorm_mono a (positiveLogMeasure_mono Measure.sub_le)).trans_lt ?_
  rw [positiveLogMeasure_positiveDilationMixture, weightedLogNorm_conv]
  exact ENNReal.mul_lt_top (weightedLogNorm_integerLogComb_lt_top ha) hp

/-- M⁺ and M⁻ live on disjoint lattice points, so (M⁺, M⁻) is the Jordan pair of M_μ and
the variation of M_μ is M⁺ + M⁻. -/
theorem moebiusComb_mutuallySingular : moebiusPlusComb ⟂ₘ moebiusMinusComb := by
  classical
  set S : Set ℝ := (fun k : ℕ => Real.log k) '' {k | ArithmeticFunction.moebius k = 1} with hS
  have hSm : MeasurableSet S := (Set.Countable.image (Set.to_countable _) _).measurableSet
  refine ⟨Sᶜ, hSm.compl, ?_, ?_⟩
  · unfold moebiusPlusComb latticeMeasure
    rw [Measure.sum_apply _ hSm.compl, ENNReal.tsum_eq_zero]
    intro k
    rw [Measure.smul_apply, smul_eq_mul]
    dsimp only
    split_ifs with hk
    · rw [Measure.dirac_apply' _ hSm.compl, Set.indicator_of_notMem, mul_zero]
      exact fun h => h ⟨k, hk, rfl⟩
    · rw [zero_mul]
  · rw [compl_compl]
    unfold moebiusMinusComb latticeMeasure
    rw [Measure.sum_apply _ hSm, ENNReal.tsum_eq_zero]
    intro k
    rw [Measure.smul_apply, smul_eq_mul]
    dsimp only
    split_ifs with hk
    · rw [Measure.dirac_apply' _ hSm, Set.indicator_of_notMem, mul_zero]
      rintro ⟨j, hj, hjk⟩
      have hj0 : j ≠ 0 := by rintro rfl; simp at hj
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk
      have hjk' : j = k := by
        have := Real.log_injOn_pos (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj0)))
          (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0))) hjk
        exact_mod_cast this
      subst hjk'
      simp only [Set.mem_ofPred_eq] at hj
      rw [hj] at hk
      norm_num at hk
    · rw [zero_mul]

/-- Original R1-HT1 root: the actual weighted Möbius inverse. For a complex mixing
measure with exponential moment a > 1/2 and its genuine mixture ν, the weighted
logarithmic pushforward η of ν restricted to the positive axis satisfies
η = N ∗ σ, the lattice identity M_μ ∗ N = δ₀ holds, and σ = M_μ ∗ η, all in
the weighted algebra of positive measures with finite norm ∫ e^(-a y), with
Jordan parts kept positive (no subtraction of infinite measures). The norm is
exactly multiplicative for the genuine product-measure convolution, with
‖N‖ = ζ(a+1/2) and ‖M_μ‖ = Σ|μ(n)| n^(-a-1/2) = ζ(a+1/2)/ζ(2a+1); here M⁺ ⟂ M⁻, so
(M⁺, M⁻) is the Jordan pair of M_μ and M⁺ + M⁻ is its variation. -/
theorem weighted_mobius_inverse (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞) :
    (∀ i : Fin 4, positiveLogMeasure (positiveDilationMixture (mixingCoordinate σ i)) =
      integerLogComb ∗ mixingCoordinate σ i) ∧
    (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
        integerLogComb ∗ σ.rePart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
        integerLogComb ∗ σ.rePart.positive) ∧
    (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive +
        integerLogComb ∗ σ.imPart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative +
        integerLogComb ∗ σ.imPart.positive) ∧
    (moebiusPlusComb ∗ integerLogComb = Measure.dirac 0 + moebiusMinusComb ∗ integerLogComb) ∧
    (σ.rePart.positive +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive) =
      σ.rePart.negative +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative)) ∧
    (σ.imPart.positive +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive) =
      σ.imPart.negative +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative)) ∧
    (∀ i : Fin 4, weightedLogNorm a (mixingCoordinate σ i) < ∞) ∧
    (weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive) < ∞ ∧
      weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative) < ∞ ∧
      weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive) < ∞ ∧
      weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative) < ∞) ∧
    (∀ (μ ρ : Measure ℝ) [SFinite ρ],
      weightedLogNorm a (μ ∗ ρ) = weightedLogNorm a μ * weightedLogNorm a ρ) ∧
    (weightedLogNorm a integerLogComb = ENNReal.ofReal (∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2))) ∧
      ((∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) = riemannZeta ((a + 1 / 2 : ℝ) : ℂ)) ∧
    (moebiusPlusComb ⟂ₘ moebiusMinusComb ∧
      weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) =
        ENNReal.ofReal (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) ∧
      ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
        riemannZeta ((a + 1 / 2 : ℝ) : ℂ) / riemannZeta ((2 * a + 1 : ℝ) : ℂ)) := by
  have hs : 1 < a + 1 / 2 := by linarith
  let m (i : Fin 4) := positiveDilationMixture (mixingCoordinate σ i)
  have hfin (i : Fin 4) : IsLocallyFiniteMeasure (m i) :=
    positiveDilationMixture_locallyFinite _ a ha.le (mixingCoordinate_moment σ a hm i)
  have := hfin 0
  have := hfin 1
  have := hfin 2
  have := hfin 3
  have hre : positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
        integerLogComb ∗ σ.rePart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
        integerLogComb ∗ σ.rePart.positive :=
    mixture_log_jordan (mixingCoordinate σ 0) (mixingCoordinate σ 1)
  have him : positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive +
        integerLogComb ∗ σ.imPart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative +
        integerLogComb ∗ σ.imPart.positive :=
    mixture_log_jordan (mixingCoordinate σ 2) (mixingCoordinate σ 3)
  have hn := weightedLogNorm_mixingCoordinate ha hm
  refine ⟨fun i => positiveLogMeasure_positiveDilationMixture _, hre, him,
    moebiusPlus_conv_integerLogComb, ?_, ?_, hn, ⟨?_, ?_, ?_, ?_⟩,
    fun μ ρ _ => weightedLogNorm_conv a μ ρ,
    ⟨weightedLogNorm_integerLogComb ha, real_tsum_rpow_eq_zeta hs⟩,
    ⟨moebiusComb_mutuallySingular, weightedLogNorm_moebiusComb ha, ?_⟩⟩
  · exact moebius_inverse_jordan ha _ _ _ _ (hn 0) (hn 1) hre
  · exact moebius_inverse_jordan ha _ _ _ _ (hn 2) (hn 3) him
  · exact mixture_log_part_norm ha (mixingCoordinate σ 0) (mixingCoordinate σ 1) (hn 0)
  · exact mixture_log_part_norm ha (mixingCoordinate σ 1) (mixingCoordinate σ 0) (hn 1)
  · exact mixture_log_part_norm ha (mixingCoordinate σ 2) (mixingCoordinate σ 3) (hn 2)
  · exact mixture_log_part_norm ha (mixingCoordinate σ 3) (mixingCoordinate σ 2) (hn 3)
  · rw [tsum_abs_moebius_rpow hs]
    congr 2
    push_cast
    ring


/-! ### Jordan uniqueness, causality and the noncompact sharp gap -/

lemma jordan_le_of_add_eq {P Q U V : Measure ℝ} (hPQ : P ⟂ₘ Q) (h : P + U = Q + V) : P ≤ V := by
  obtain ⟨s, hs, hPs, hQs⟩ := hPQ
  refine Measure.le_iff.mpr (fun E hE => ?_)
  have hsplit : P E = P (E ∩ sᶜ) := by
    have h1 : P (E ∩ s) = 0 := measure_mono_null inter_subset_right hPs
    rw [← measure_inter_add_sdiff E hs, h1, zero_add, sdiff_eq]
  have hE' := congrArg (fun μ : Measure ℝ => μ (E ∩ sᶜ)) h
  simp only [Measure.add_apply] at hE'
  have hQ0 : Q (E ∩ sᶜ) = 0 := measure_mono_null inter_subset_right hQs
  rw [hQ0, zero_add] at hE'
  calc P E = P (E ∩ sᶜ) := hsplit
    _ ≤ P (E ∩ sᶜ) + U (E ∩ sᶜ) := le_self_add
    _ = V (E ∩ sᶜ) := hE'
    _ ≤ V E := measure_mono inter_subset_left

lemma jordan_unique {P Q P' Q' X Y : Measure ℝ} (hPQ : P ⟂ₘ Q) (hPQ' : P' ⟂ₘ Q')
    (hXY : ∀ R : ℝ, (X + Y) (Icc (-R) R) < ∞)
    (h1 : P + X = Q + Y) (h2 : P' + X = Q' + Y) : P = P' ∧ Q = Q' := by
  have hcross : P + Q' = Q + P' := by
    refine measure_add_right_cancel_of_Icc hXY ?_
    calc P + Q' + (X + Y) = (P + X) + (Q' + Y) := by abel
      _ = (Q + Y) + (P' + X) := by rw [h1, ← h2]
      _ = Q + P' + (X + Y) := by abel
  have hcross' : P' + Q = Q' + P := by
    calc P' + Q = Q + P' := add_comm _ _
      _ = P + Q' := hcross.symm
      _ = Q' + P := add_comm _ _
  refine ⟨le_antisymm (jordan_le_of_add_eq hPQ hcross) (jordan_le_of_add_eq hPQ' hcross'), ?_⟩
  have h3 : Q + P' = P + Q' := hcross.symm
  have h4 : Q' + P = P' + Q := hcross'.symm
  exact le_antisymm (jordan_le_of_add_eq hPQ.symm h3) (jordan_le_of_add_eq hPQ'.symm h4)

lemma positiveLogMeasure_Iio_eq_zero {ρ : Measure ℝ} (h : ρ (Ioo 0 1) = 0) :
    positiveLogMeasure ρ (Iio 0) = 0 := by
  have hf : Measurable ((Iio (0 : ℝ)).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Iio
  rw [← lintegral_indicator_one measurableSet_Iio, lintegral_positiveLogMeasure _ hf]
  refine le_antisymm ?_ zero_le
  calc _ ≤ ∫⁻ x, (Ioo (0 : ℝ) 1).indicator (fun _ => ∞) x ∂ρ := by
        refine lintegral_mono (fun x => ?_)
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hx]
          by_cases hx1 : x < 1
          · rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from ⟨hx, hx1⟩)]
            exact le_top
          · have hlog : ¬ Real.log x < 0 := by
              rw [not_lt]; exact Real.log_nonneg (not_lt.mp hx1)
            simp [Set.indicator_of_notMem (show Real.log x ∉ Iio (0 : ℝ) from hlog)]
        · rw [Set.indicator_of_notMem hx]; exact zero_le
    _ = 0 := by
        rw [lintegral_indicator measurableSet_Ioo, setLIntegral_measure_zero _ _ h]

lemma latticeMeasure_conv_Iio_eq_zero (w : ℕ → ℝ≥0∞) (hw : w 0 = 0) (ρ : Measure ℝ)
    [SFinite ρ] (h : ρ (Iio 0) = 0) : (latticeMeasure w ∗ ρ) (Iio 0) = 0 := by
  rw [latticeMeasure_conv_apply _ _ measurableSet_Iio]
  refine ENNReal.tsum_eq_zero.mpr (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hw]
  · have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
    have hsub : (fun y => Real.log k + y) ⁻¹' Iio 0 ⊆ Iio 0 := by
      intro y hy
      simp only [mem_preimage, mem_Iio] at hy ⊢
      linarith
    rw [measure_mono_null hsub h, mul_zero]

lemma moebiusComb_conv_Iio_eq_zero (ρ : Measure ℝ) [SFinite ρ] (h : ρ (Iio 0) = 0) :
    (moebiusPlusComb ∗ ρ) (Iio 0) = 0 ∧ (moebiusMinusComb ∗ ρ) (Iio 0) = 0 :=
  ⟨latticeMeasure_conv_Iio_eq_zero _ (by simp) ρ h,
    latticeMeasure_conv_Iio_eq_zero _ (by simp) ρ h⟩

lemma measure_eq_dirac_zero {μ : Measure ℝ} (hneg : μ (Iio 0) = 0) (hpos : μ (Ioi 0) = 0) :
    μ = μ {0} • Measure.dirac 0 := by
  ext s hs
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  have hcompl : μ ({0}ᶜ) = 0 := by
    rw [← Set.Iio_union_Ioi]
    exact measure_union_null hneg hpos
  have hsplit := measure_inter_add_sdiff s (measurableSet_singleton (0 : ℝ)) (μ := μ)
  have hdiff : μ (s \ {0}) = 0 := measure_mono_null (fun x hx => hx.2) hcompl
  rw [hdiff, add_zero] at hsplit
  rw [← hsplit]
  by_cases h0 : (0 : ℝ) ∈ s
  · rw [Set.indicator_of_mem h0, Pi.one_apply, mul_one,
      inter_eq_right.mpr (singleton_subset_iff.mpr h0)]
  · rw [Set.indicator_of_notMem h0, mul_zero, Set.inter_singleton_eq_empty.mpr h0, measure_empty]

lemma measure_null_of_le {μ ν : Measure ℝ} (h : μ ≤ ν) {s : Set ℝ} (hs : ν s = 0) : μ s = 0 :=
  le_antisymm ((Measure.le_iff'.mp h s).trans hs.le) zero_le

lemma reflected_apply_Ioi (μ : Measure ℝ) :
    reflectedMixingPositiveMeasure μ (Ioi 0) = μ (Iio 0) := by
  rw [reflectedMixingPositiveMeasure, Measure.map_apply measurable_neg measurableSet_Ioi]
  congr 1
  ext x
  simp

/-- One Jordan pair of an even mixing measure is concentrated at the origin when
both lattice correction terms vanish on the negative axis. -/
lemma jordan_pair_concentrated {P Q X Y : Measure ℝ} (hPQ : P ⟂ₘ Q)
    (hPQr : reflectedMixingPositiveMeasure P ⟂ₘ reflectedMixingPositiveMeasure Q)
    (hXY : ∀ R : ℝ, (X + Y) (Icc (-R) R) < ∞)
    (h1 : P + X = Q + Y)
    (h2 : reflectedMixingPositiveMeasure P + X = reflectedMixingPositiveMeasure Q + Y)
    (hX : X (Iio 0) = 0) (hY : Y (Iio 0) = 0) :
    P (Iio 0) = 0 ∧ P (Ioi 0) = 0 ∧ Q (Iio 0) = 0 ∧ Q (Ioi 0) = 0 := by
  obtain ⟨hPe, hQe⟩ := jordan_unique hPQ hPQr hXY h1 h2
  have hPn : P (Iio 0) = 0 :=
    measure_null_of_le (jordan_le_of_add_eq hPQ h1) hY
  have hQn : Q (Iio 0) = 0 :=
    measure_null_of_le (jordan_le_of_add_eq hPQ.symm h1.symm) hX
  refine ⟨hPn, ?_, hQn, ?_⟩
  · rw [hPe, reflected_apply_Ioi, hPn]
  · rw [hQe, reflected_apply_Ioi, hQn]

lemma complexIntegral_point_mass (σ : LocallyFiniteComplexMeasure)
    (hpt : ∀ i : Fin 4, mixingCoordinate σ i = mixingCoordinate σ i {0} • Measure.dirac 0)
    (g : ℝ → ℂ) : σ.integral g = g 0 * σ.integral (fun _ => 1) := by
  unfold LocallyFiniteComplexMeasure.integral
  rw [show σ.rePart.positive = _ from hpt 0, show σ.rePart.negative = _ from hpt 1,
    show σ.imPart.positive = _ from hpt 2, show σ.imPart.negative = _ from hpt 3]
  simp only [integral_smul_measure, integral_dirac, Complex.real_smul]
  ring

lemma point_masses_singular_zero {c d : ℝ≥0∞}
    (h : (c • Measure.dirac (0 : ℝ)) ⟂ₘ (d • Measure.dirac 0)) : c = 0 ∨ d = 0 := by
  obtain ⟨s, hs, h1, h2⟩ := h
  by_cases h0 : (0 : ℝ) ∈ s
  · left
    simpa [Measure.dirac_apply' _ hs, h0] using h1
  · right
    simpa [Measure.dirac_apply' _ hs.compl, h0] using h2

lemma positiveDilationMixture_zero : positiveDilationMixture (0 : Measure ℝ) = 0 := by
  simp [positiveDilationMixture]

/-- Original R1-HT1 root: the noncompact sharp gap. If the genuine weighted
mixture of a complex mixer with exponential moment a > 1/2 is Fourier self-dual
and its restriction to (-1,1) \ {0} vanishes, then the mixer is a point mass c δ₀,
the mixture is c times the integer comb D₀ = dilatedCombDistribution 0 with
c its origin atom, and a zero origin atom forces mixer and mixture to vanish.
No positivity premise is used; the strict threshold a > 1/2 is retained. -/
theorem weighted_mixture_sharp_gap (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞)
    (hself : 𝓕 ((weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm)) =
      (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm))
    (hgap : (weightedDilationMixture σ a ha.le hm).variationControl (Ioo (-1) 1 \ {0}) = 0) :
    (∀ i : Fin 4, mixingCoordinate σ i = mixingCoordinate σ i {0} • Measure.dirac 0) ∧
    σ.variationControl ({0}ᶜ) = 0 ∧
    (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm) =
      σ.integral (fun _ => 1) • dilatedCombDistribution 0 ∧
    (weightedDilationMixture σ a ha.le hm).compactRestriction {0} isCompact_singleton {0} =
      σ.integral (fun _ => 1) ∧
    ((weightedDilationMixture σ a ha.le hm).compactRestriction {0} isCompact_singleton {0} = 0 →
      (∀ i : Fin 4, mixingCoordinate σ i = 0) ∧
      (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm) = 0 ∧
      (weightedDilationMixture σ a ha.le hm).variationControl = 0) := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  set ν := weightedDilationMixture σ a ha.le hm with hνdef
  have hm' := mixingExponentialMoment_reflect_lt_top σ a hm
  -- self-duality and faithfulness give ν_(σ^∨) = ν_σ
  have hdist : (weightedDilationMixture (reflectedMixingMeasure σ) a ha.le hm').distributionOfLinearGrowth
      (weightedDilationMixture_growth _ a ha.le hm') =
      ν.distributionOfLinearGrowth (weightedDilationMixture_growth σ a ha.le hm) := by
    rw [← weightedDilationMixture_fourier σ a ha.le hm, hself]
  have hνr : weightedDilationMixture (reflectedMixingMeasure σ) a ha.le hm' = ν :=
    congrArg Subtype.val (LocallyFiniteComplexMeasure.distributionOfLinearGrowth_injective
      (a₁ := ⟨_, weightedDilationMixture_growth _ a ha.le hm'⟩)
      (a₂ := ⟨ν, weightedDilationMixture_growth σ a ha.le hm⟩) hdist)
  obtain ⟨-, -, -, -, hinvre, hinvim, -, ⟨hηrp, hηrn, hηip, hηin⟩, -, -, ⟨-, hMnorm, -⟩⟩ :=
    weighted_mobius_inverse σ a ha hm
  obtain ⟨-, -, -, -, hinvre', hinvim', -⟩ :=
    weighted_mobius_inverse (reflectedMixingMeasure σ) a ha hm'
  rw [hνr] at hinvre' hinvim'
  -- finiteness of the correction terms on bounded sets
  have hM := weightedLogNorm_moebiusComb_lt_top ha
  have hfinXY (ηp ηn : Measure ℝ) [SFinite ηp] [SFinite ηn]
      (hp : weightedLogNorm a ηp < ∞) (hn : weightedLogNorm a ηn < ∞) (R : ℝ) :
      ((moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) +
        (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn)) (Icc (-R) R) < ∞ := by
    refine measure_Icc_lt_top_of_weightedLogNorm ha0 ?_ R
    simp only [weightedLogNorm_add, weightedLogNorm_conv]
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hM.1 hn, ENNReal.mul_lt_top hM.2 hp⟩,
        ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hM.1 hp, ENNReal.mul_lt_top hM.2 hn⟩⟩
  -- the gap empties every η part on the negative axis
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioo (-1) 1 \ {0} := fun x hx =>
    ⟨⟨by linarith [hx.1], hx.2⟩, by simpa using hx.1.ne'⟩
  have hgap0 : ν.variationControl (Ioo 0 1) = 0 := measure_mono_null hsub hgap
  have hpart (ρ : Measure ℝ) (hle : ρ ≤ ν.variationControl) : positiveLogMeasure ρ (Iio 0) = 0 :=
    positiveLogMeasure_Iio_eq_zero (measure_null_of_le hle hgap0)
  have hrp : ν.rePart.positive ≤ ν.variationControl :=
    (weightedJordanPositive_le_totalVariation _).trans (weightedReal_le_control _)
  have hrn : ν.rePart.negative ≤ ν.variationControl :=
    (weightedJordanNegative_le_totalVariation _).trans (weightedReal_le_control _)
  have hip : ν.imPart.positive ≤ ν.variationControl :=
    (weightedJordanPositive_le_totalVariation _).trans (weightedImaginary_le_control _)
  have hin : ν.imPart.negative ≤ ν.variationControl :=
    (weightedJordanNegative_le_totalVariation _).trans (weightedImaginary_le_control _)
  have hvanish (ηp ηn : Measure ℝ) [SFinite ηp] [SFinite ηn]
      (hp : ηp (Iio 0) = 0) (hn : ηn (Iio 0) = 0) :
      (moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) (Iio 0) = 0 ∧
      (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn) (Iio 0) = 0 := by
    simp only [Measure.add_apply, (moebiusComb_conv_Iio_eq_zero _ hp).1,
      (moebiusComb_conv_Iio_eq_zero _ hp).2, (moebiusComb_conv_Iio_eq_zero _ hn).1,
      (moebiusComb_conv_Iio_eq_zero _ hn).2, add_zero, and_self]
  have hre := jordan_pair_concentrated σ.rePart.mutuallySingular
    (reflectedMixingMeasure σ).rePart.mutuallySingular (hfinXY _ _ hηrp hηrn) hinvre hinvre'
    (hvanish _ _ (hpart _ hrp) (hpart _ hrn)).1 (hvanish _ _ (hpart _ hrp) (hpart _ hrn)).2
  have him := jordan_pair_concentrated σ.imPart.mutuallySingular
    (reflectedMixingMeasure σ).imPart.mutuallySingular (hfinXY _ _ hηip hηin) hinvim hinvim'
    (hvanish _ _ (hpart _ hip) (hpart _ hin)).1 (hvanish _ _ (hpart _ hip) (hpart _ hin)).2
  have hpt : ∀ i : Fin 4, mixingCoordinate σ i = mixingCoordinate σ i {0} • Measure.dirac 0 := by
    intro i
    fin_cases i
    · exact measure_eq_dirac_zero hre.1 hre.2.1
    · exact measure_eq_dirac_zero hre.2.2.1 hre.2.2.2
    · exact measure_eq_dirac_zero him.1 him.2.1
    · exact measure_eq_dirac_zero him.2.2.1 him.2.2.2
  have hcompl (μ : Measure ℝ) (h1 : μ (Iio 0) = 0) (h2 : μ (Ioi 0) = 0) : μ ({0}ᶜ) = 0 := by
    rw [← Set.Iio_union_Ioi]; exact measure_union_null h1 h2
  have hdistr : ν.distributionOfLinearGrowth (weightedDilationMixture_growth σ a ha.le hm) =
      σ.integral (fun _ => 1) • dilatedCombDistribution 0 := by
    ext1 f
    change ν.integral f = σ.integral (fun _ => 1) * dilatedCombDistribution 0 f
    rw [weightedDilationMixture_pairing, complexIntegral_point_mass σ hpt, mul_comm]
  have horigin : ν.compactRestriction {0} isCompact_singleton {0} = σ.integral (fun _ => 1) := by
    rw [weightedDilationMixture_origin, complexIntegral_point_mass σ hpt]
    simp
  refine ⟨hpt, ?_, hdistr, horigin, fun h0 => ?_⟩
  · change ((σ.rePart.positive + σ.rePart.negative) + (σ.imPart.positive + σ.imPart.negative))
      ({0}ᶜ) = 0
    simp only [Measure.add_apply, hcompl _ hre.1 hre.2.1, hcompl _ hre.2.2.1 hre.2.2.2,
      hcompl _ him.1 him.2.1, hcompl _ him.2.2.1 him.2.2.2, add_zero]
  · rw [horigin] at h0
    have hval := h0
    rw [show σ.integral (fun _ => 1) = σ.integral (fun _ => 1) from rfl] at hval
    unfold LocallyFiniteComplexMeasure.integral at hval
    rw [show σ.rePart.positive = _ from hpt 0, show σ.rePart.negative = _ from hpt 1,
      show σ.imPart.positive = _ from hpt 2, show σ.imPart.negative = _ from hpt 3] at hval
    simp only [integral_smul_measure, integral_dirac, Complex.real_smul, mul_one] at hval
    have hre0 := congrArg Complex.re hval
    have him0 := congrArg Complex.im hval
    simp at hre0 him0
    have hfin (i : Fin 4) : mixingCoordinate σ i {0} ≠ ∞ :=
      (isCompact_singleton.measure_lt_top (μ := mixingCoordinate σ i)).ne
    have hs01 := σ.rePart.mutuallySingular
    rw [show σ.rePart.positive = _ from hpt 0, show σ.rePart.negative = _ from hpt 1] at hs01
    have hs23 := σ.imPart.mutuallySingular
    rw [show σ.imPart.positive = _ from hpt 2, show σ.imPart.negative = _ from hpt 3] at hs23
    have hsing01 := point_masses_singular_zero hs01
    have hsing23 := point_masses_singular_zero hs23
    have hz01 : mixingCoordinate σ 0 {0} = 0 ∧ mixingCoordinate σ 1 {0} = 0 := by
      rcases hsing01 with h | h
      · refine ⟨h, ?_⟩
        rw [h, ENNReal.toReal_zero] at hre0
        exact (ENNReal.toReal_eq_zero_iff _).mp (by linarith) |>.resolve_right (hfin 1)
      · refine ⟨?_, h⟩
        rw [h, ENNReal.toReal_zero] at hre0
        exact (ENNReal.toReal_eq_zero_iff _).mp (by linarith) |>.resolve_right (hfin 0)
    have hz23 : mixingCoordinate σ 2 {0} = 0 ∧ mixingCoordinate σ 3 {0} = 0 := by
      rcases hsing23 with h | h
      · refine ⟨h, ?_⟩
        rw [h, ENNReal.toReal_zero] at him0
        exact (ENNReal.toReal_eq_zero_iff _).mp (by linarith) |>.resolve_right (hfin 3)
      · refine ⟨?_, h⟩
        rw [h, ENNReal.toReal_zero] at him0
        exact (ENNReal.toReal_eq_zero_iff _).mp (by linarith) |>.resolve_right (hfin 2)
    have hzero : ∀ i : Fin 4, mixingCoordinate σ i = 0 := by
      intro i
      fin_cases i
      · show mixingCoordinate σ 0 = 0
        rw [hpt 0, hz01.1, zero_smul]
      · show mixingCoordinate σ 1 = 0
        rw [hpt 1, hz01.2, zero_smul]
      · show mixingCoordinate σ 2 = 0
        rw [hpt 2, hz23.1, zero_smul]
      · show mixingCoordinate σ 3 = 0
        rw [hpt 3, hz23.2, zero_smul]
    refine ⟨hzero, ?_, ?_⟩
    · exact hdistr.trans (by rw [h0]; ext1 f; simp)
    · change ((positiveDilationMixture (mixingCoordinate σ 0) -
          positiveDilationMixture (mixingCoordinate σ 1)) +
        (positiveDilationMixture (mixingCoordinate σ 1) -
          positiveDilationMixture (mixingCoordinate σ 0))) +
        ((positiveDilationMixture (mixingCoordinate σ 2) -
          positiveDilationMixture (mixingCoordinate σ 3)) +
        (positiveDilationMixture (mixingCoordinate σ 3) -
          positiveDilationMixture (mixingCoordinate σ 2))) = 0
      simp only [hzero, positiveDilationMixture_zero, Measure.sub_self, add_zero]


/-! ### Quantitative gap leakage (measure form) -/

lemma latticeMeasure_conv_restrict_Iio (w : ℕ → ℝ≥0∞) (hw : w 0 = 0) (ρ : Measure ℝ)
    [SFinite ρ] :
    (latticeMeasure w ∗ ρ).restrict (Iio 0) ≤ latticeMeasure w ∗ ρ.restrict (Iio 0) := by
  refine Measure.le_iff.mpr (fun E hE => ?_)
  rw [Measure.restrict_apply hE, latticeMeasure_conv_apply _ _ (hE.inter measurableSet_Iio),
    latticeMeasure_conv_apply _ _ hE]
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hw]
  · have hsub : ρ ((fun y => Real.log k + y) ⁻¹' (E ∩ Iio 0)) ≤
        (ρ.restrict (Iio 0)) ((fun y => Real.log k + y) ⁻¹' E) := by
      rw [Measure.restrict_apply (measurable_const_add _ hE)]
      refine measure_mono (fun y hy => ⟨hy.1, ?_⟩)
      have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
      have h2 : Real.log k + y < 0 := hy.2
      show y < 0
      linarith
    exact mul_le_mul le_rfl hsub zero_le zero_le

lemma setLIntegral_positiveLogMeasure_Iio (a : ℝ) (ρ : Measure ℝ) :
    ∫⁻ y in Iio 0, ENNReal.ofReal (Real.exp (-a * y)) ∂positiveLogMeasure ρ =
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2)) ∂ρ := by
  have hf : Measurable ((Iio (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp (-a * y)))) :=
    (by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (-a * y))).indicator
      measurableSet_Iio
  rw [← lintegral_indicator measurableSet_Iio, lintegral_positiveLogMeasure _ hf,
    ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr (fun x => ?_)
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · have hx0 : x ∈ Ioi (0 : ℝ) := hx.1
    have hlog : Real.log x ∈ Iio (0 : ℝ) := Real.log_neg hx.1 hx.2
    rw [Set.indicator_of_mem hx0, Set.indicator_of_mem hlog, Set.indicator_of_mem hx]
    simp only [positiveLogWeight, if_pos hx.1]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.1.le, mul_comm (-a), ← Real.rpow_def_of_pos hx.1,
      ← Real.rpow_add hx.1]
    ring_nf
  · rw [Set.indicator_of_notMem hx]
    by_cases hx0 : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx0]
      have hlog : Real.log x ∉ Iio (0 : ℝ) := by
        simp only [mem_Iio, not_lt]
        refine Real.log_nonneg ?_
        by_contra h
        exact hx ⟨hx0, lt_of_not_ge h⟩
      rw [Set.indicator_of_notMem hlog, mul_zero]
    · rw [Set.indicator_of_notMem hx0]

lemma tsum_abs_moebius_rpow_pos {s : ℝ} (hs : 1 < s) :
    0 < ∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-s) := by
  have hsum : Summable (fun n : ℕ => (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-s)) := by
    refine (summable_nat_rpow_neg hs).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    have h' : (|ArithmeticFunction.moebius n| : ℝ) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc _ ≤ 1 * (n : ℝ) ^ (-s) := mul_le_mul_of_nonneg_right h' (by positivity)
      _ = _ := one_mul _
  refine lt_of_lt_of_le ?_ (hsum.le_tsum 1 (fun n _ => by positivity))
  simp

lemma zeta_ratio_re {s : ℝ} (hs : 1 < s) :
    (riemannZeta ((2 * s : ℝ) : ℂ) / riemannZeta (s : ℂ)).re =
      (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-s))⁻¹ := by
  have h := tsum_abs_moebius_rpow hs
  have hz : riemannZeta (s : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  have hz2 : riemannZeta ((2 * s : ℝ) : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hcast : ((2 * s : ℝ) : ℂ) = 2 * (s : ℂ) := by push_cast; ring
  rw [hcast, ← inv_div, ← h, ← Complex.ofReal_inv, Complex.ofReal_re]

/-- Leakage for one Jordan pair: the negative-axis weighted variation of the mixer
is bounded by ‖M_μ‖ times the interior-gap variation of η. -/
theorem jordan_gap_leakage (a : ℝ) {P Q ηp ηn : Measure ℝ}
    [SFinite ηp] [SFinite ηn] (hPQ : P ⟂ₘ Q)
    (h : P + (moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) =
      Q + (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn)) :
    ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂(P + Q) ≤
      weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) *
        ∫⁻ y in Iio 0, ENNReal.ofReal (Real.exp (-a * y)) ∂(ηp + ηn) := by
  have hle : P + Q ≤ (moebiusPlusComb + moebiusMinusComb) ∗ (ηp + ηn) := by
    have h1 := jordan_le_of_add_eq hPQ h
    have h2 := jordan_le_of_add_eq hPQ.symm h.symm
    calc P + Q ≤ (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn) +
          (moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) := add_le_add h1 h2
      _ = (moebiusPlusComb + moebiusMinusComb) ∗ (ηp + ηn) := by
          rw [Measure.add_conv, Measure.conv_add, Measure.conv_add]; abel
  have hcaus : ((moebiusPlusComb + moebiusMinusComb) ∗ (ηp + ηn)).restrict (Iio 0) ≤
      (moebiusPlusComb + moebiusMinusComb) ∗ (ηp + ηn).restrict (Iio 0) := by
    have hw : (fun k => (if ArithmeticFunction.moebius k = 1 then latticeWeight k else 0) +
        (if ArithmeticFunction.moebius k = -1 then latticeWeight k else 0)) 0 = 0 := by simp
    have hsum : moebiusPlusComb + moebiusMinusComb = latticeMeasure (fun k =>
        (if ArithmeticFunction.moebius k = 1 then latticeWeight k else 0) +
        (if ArithmeticFunction.moebius k = -1 then latticeWeight k else 0)) := by
      unfold moebiusPlusComb moebiusMinusComb latticeMeasure
      rw [Measure.sum_add_sum]
      simp_rw [add_smul]
    rw [hsum]
    exact latticeMeasure_conv_restrict_Iio _ hw _
  calc ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂(P + Q)
      ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t))
          ∂((moebiusPlusComb + moebiusMinusComb) ∗ (ηp + ηn)).restrict (Iio 0) :=
        lintegral_mono' (Measure.restrict_mono subset_rfl hle) le_rfl
    _ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t))
          ∂((moebiusPlusComb + moebiusMinusComb) ∗ (ηp + ηn).restrict (Iio 0)) :=
        lintegral_mono' hcaus le_rfl
    _ = _ := weightedLogNorm_conv a _ _

/-! ### Continuous-density supremum counterpart (HT1.8-HT1.9) -/

/-- Real lattice weight k^(-1/2), zero at k = 0. -/
def latticeWeightR (k : ℕ) : ℝ := if k = 0 then 0 else (Real.sqrt k)⁻¹

lemma latticeWeightR_nonneg (k : ℕ) : 0 ≤ latticeWeightR k := by
  unfold latticeWeightR; split_ifs <;> positivity

lemma latticeWeightR_mul {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    latticeWeightR i * latticeWeightR j = latticeWeightR (i * j) := by
  simp only [latticeWeightR, if_neg hi, if_neg hj, if_neg (mul_ne_zero hi hj)]
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]

lemma latticeWeightR_rpow {b : ℝ} (hb : 0 < b + 1 / 2) (k : ℕ) :
    latticeWeightR k * Real.exp (-b * Real.log k) = (k : ℝ) ^ (-(b + 1 / 2)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]; simp [latticeWeightR]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [latticeWeightR, if_neg hk.ne']
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hk'.le, mul_comm (-b), ← Real.rpow_def_of_pos hk',
      ← Real.rpow_add hk']
    ring_nf

/-- The lattice transform g = N ∗ h of a function. -/
def latticeTransform (h : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∑' n : ℕ, (latticeWeightR n : ℂ) * h (y - Real.log n)

/-- The paper's positive-axis mixture density r_h(x) = x^(-1/2) Σ h(log(x/n)) n^(-1/2). -/
def mixtureDensity (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((Real.sqrt x)⁻¹ : ℝ) * ∑' n : ℕ, (latticeWeightR n : ℂ) * h (Real.log (x / n))

lemma mixtureDensity_exp (h : ℝ → ℂ) (y : ℝ) :
    ((Real.exp (y / 2) : ℝ) : ℂ) * mixtureDensity h (Real.exp y) = latticeTransform h y := by
  unfold mixtureDensity latticeTransform
  rw [← mul_assoc, ← Complex.ofReal_mul]
  have hsq : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
    rw [show Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) by rw [← Real.exp_add]; ring_nf,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [hsq, mul_inv_cancel₀ (Real.exp_pos _).ne', Complex.ofReal_one, one_mul]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [latticeWeightR]
  · rw [Real.log_div (Real.exp_pos _).ne' (by exact_mod_cast hn.ne'), Real.log_exp]

lemma decay_bound_nonpos {h : ℝ → ℂ} {H b : ℝ} (hdecay : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|))
    {z : ℝ} (hz : z ≤ 0) : ‖h z‖ ≤ H * Real.exp (b * z) := by
  have := hdecay z
  rwa [abs_of_nonpos hz, neg_mul_neg] at this

/-- Absolute double-series Möbius inversion of the lattice transform on y ≤ 0. -/
theorem latticeTransform_moebius_inverse {h : ℝ → ℂ} {H b : ℝ} (hb : 1 / 2 < b)
    (hdecay : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) {y : ℝ} (hy : y ≤ 0) :
    ∑' m : ℕ, ((ArithmeticFunction.moebius m : ℝ) : ℂ) * (latticeWeightR m : ℂ) *
      latticeTransform h (y - Real.log m) = h y := by
  have hs : 1 < b + 1 / 2 := by linarith
  set F : ℕ × ℕ → ℂ := fun p => ((ArithmeticFunction.moebius p.1 : ℝ) : ℂ) *
    (latticeWeightR p.1 : ℂ) * ((latticeWeightR p.2 : ℂ) * h (y - Real.log p.1 - Real.log p.2))
    with hFdef
  have hF0 : ∀ p : ℕ × ℕ, p.1 = 0 ∨ p.2 = 0 → F p = 0 := by
    rintro ⟨i, j⟩ (h0 | h0) <;> simp only at h0 <;> simp [hFdef, h0, latticeWeightR]
  -- domination by a product of summable weights
  have hbound (p : ℕ × ℕ) : ‖F p‖ ≤ (H * Real.exp (b * y)) *
      ((p.1 : ℝ) ^ (-(b + 1 / 2)) * (p.2 : ℝ) ^ (-(b + 1 / 2))) := by
    rcases p with ⟨i, j⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hF0 _ (Or.inl rfl), norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), zero_mul, mul_zero]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hF0 _ (Or.inr rfl), norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero, mul_zero]
    have hli : 0 ≤ Real.log i := Real.log_nonneg (by exact_mod_cast hi)
    have hlj : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
    have hz : y - Real.log i - Real.log j ≤ 0 := by linarith
    have hμ : |(ArithmeticFunction.moebius i : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hhz := decay_bound_nonpos hdecay hz
    have hexp : Real.exp (b * (y - Real.log i - Real.log j)) =
        Real.exp (b * y) * (Real.exp (-b * Real.log i) * Real.exp (-b * Real.log j)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hwi := latticeWeightR_rpow (by linarith : 0 < b + 1 / 2) i
    have hwj := latticeWeightR_rpow (by linarith : 0 < b + 1 / 2) j
    have hwi0 := latticeWeightR_nonneg i
    have hwj0 := latticeWeightR_nonneg j
    have key : ‖F (i, j)‖ = |(ArithmeticFunction.moebius i : ℝ)| * latticeWeightR i *
        (latticeWeightR j * ‖h (y - Real.log i - Real.log j)‖) := by
      simp only [hFdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hwi0, abs_of_nonneg hwj0]
    calc ‖F (i, j)‖ = _ := key
      _ ≤ 1 * latticeWeightR i * (latticeWeightR j * (H * Real.exp (b * (y - Real.log i -
            Real.log j)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hμ hwi0) (mul_le_mul_of_nonneg_left hhz hwj0)
            (mul_nonneg hwj0 (norm_nonneg _)) (by rw [one_mul]; exact hwi0)
      _ = (H * Real.exp (b * y)) * ((latticeWeightR i * Real.exp (-b * Real.log i)) *
          (latticeWeightR j * Real.exp (-b * Real.log j))) := by rw [hexp]; ring
      _ = _ := by rw [hwi, hwj]
  have hsumR := summable_nat_rpow_neg hs
  have hsumP : Summable (fun p : ℕ × ℕ =>
      (p.1 : ℝ) ^ (-(b + 1 / 2)) * (p.2 : ℝ) ^ (-(b + 1 / 2))) :=
    hsumR.mul_of_nonneg hsumR (fun _ => by positivity) (fun _ => by positivity)
  have hsum : Summable F := (hsumP.mul_left (H * Real.exp (b * y))).of_norm_bounded hbound
  -- rewrite the left side as the double series
  have hleft : ∑' m : ℕ, ((ArithmeticFunction.moebius m : ℝ) : ℂ) * (latticeWeightR m : ℂ) *
      latticeTransform h (y - Real.log m) = ∑' p, F p := by
    rw [hsum.tsum_prod]
    refine tsum_congr (fun m => ?_)
    unfold latticeTransform
    rw [← tsum_mul_left]
  rw [hleft]
  -- reindex by products
  have hpos : ∑' p : ℕ × ℕ, F p = ∑' p : ℕ+ × ℕ+, F ((p.1 : ℕ), (p.2 : ℕ)) := by
    let e : ℕ+ × ℕ+ → ℕ × ℕ := fun p => ((p.1 : ℕ), (p.2 : ℕ))
    have he : Function.Injective e := by
      intro p q hpq
      simp only [e, Prod.mk.injEq] at hpq
      exact Prod.ext (PNat.coe_injective hpq.1) (PNat.coe_injective hpq.2)
    refine (he.tsum_eq ?_).symm
    intro p hp
    rw [Function.mem_support] at hp
    have h1 : p.1 ≠ 0 := fun h0 => hp (hF0 p (Or.inl h0))
    have h2 : p.2 ≠ 0 := fun h0 => hp (hF0 p (Or.inr h0))
    exact ⟨(⟨p.1, Nat.pos_of_ne_zero h1⟩, ⟨p.2, Nat.pos_of_ne_zero h2⟩), rfl⟩
  have hsumPN : Summable (fun p : ℕ+ × ℕ+ => F ((p.1 : ℕ), (p.2 : ℕ))) := by
    have he : Function.Injective (fun p : ℕ+ × ℕ+ => ((p.1 : ℕ), (p.2 : ℕ))) := by
      intro p q hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext (PNat.coe_injective hpq.1) (PNat.coe_injective hpq.2)
    exact hsum.comp_injective he
  rw [hpos, ← sigmaAntidiagonalEquivProd.tsum_eq]
  have hsig : Summable (fun c : (Σ n : ℕ+, Nat.divisorsAntidiagonal (n : ℕ)) =>
      F (((sigmaAntidiagonalEquivProd c).1 : ℕ), ((sigmaAntidiagonalEquivProd c).2 : ℕ))) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hsumPN
  rw [hsig.tsum_sigma]
  -- each fibre contributes w(k) h(y - log k) Σ_(d|k) μ(d)
  have hfibre (k : ℕ+) : ∑' x : Nat.divisorsAntidiagonal (k : ℕ),
      F (((sigmaAntidiagonalEquivProd ⟨k, x⟩).1 : ℕ), ((sigmaAntidiagonalEquivProd ⟨k, x⟩).2 : ℕ)) =
      if (k : ℕ) = 1 then h y else 0 := by
    rw [tsum_fintype]
    have hx (x : Nat.divisorsAntidiagonal (k : ℕ)) :
        F (((sigmaAntidiagonalEquivProd ⟨k, x⟩).1 : ℕ), ((sigmaAntidiagonalEquivProd ⟨k, x⟩).2 : ℕ)) =
        ((ArithmeticFunction.moebius x.1.1 : ℝ) : ℂ) * ((latticeWeightR k : ℂ) *
          h (y - Real.log k)) := by
      have hmem := Nat.mem_divisorsAntidiagonal.mp x.2
      have hk0 : x.1.1 * x.1.2 ≠ 0 := by rw [hmem.1]; exact hmem.2
      have h1 : x.1.1 ≠ 0 := left_ne_zero_of_mul hk0
      have h2 : x.1.2 ≠ 0 := right_ne_zero_of_mul hk0
      have hw : latticeWeightR x.1.1 * latticeWeightR x.1.2 = latticeWeightR k := by
        rw [latticeWeightR_mul h1 h2, hmem.1]
      have hwc : ((latticeWeightR x.1.1 : ℝ) : ℂ) * (latticeWeightR x.1.2 : ℂ) =
          (latticeWeightR k : ℂ) := by rw [← Complex.ofReal_mul, hw]
      change F (x.1.1, x.1.2) = _
      simp only [hFdef]
      rw [sub_sub, ← Real.log_mul (by exact_mod_cast h1) (by exact_mod_cast h2), ← Nat.cast_mul,
        hmem.1]
      linear_combination (((ArithmeticFunction.moebius x.1.1 : ℝ) : ℂ) * h (y - Real.log k)) * hwc
    simp_rw [hx]
    rw [← Finset.sum_mul]
    have hsumμ : ∑ x : Nat.divisorsAntidiagonal (k : ℕ),
        ((ArithmeticFunction.moebius x.1.1 : ℝ) : ℂ) =
        ∑ d ∈ (k : ℕ).divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) := by
      rw [Finset.sum_coe_sort (Nat.divisorsAntidiagonal (k : ℕ))
        (fun p => ((ArithmeticFunction.moebius p.1 : ℝ) : ℂ))]
      rw [Nat.sum_divisorsAntidiagonal (fun i _ => ((ArithmeticFunction.moebius i : ℝ) : ℂ))]
    rw [hsumμ]
    have hcast : ∑ d ∈ (k : ℕ).divisors, ((ArithmeticFunction.moebius d : ℝ) : ℂ) =
        ((∑ d ∈ (k : ℕ).divisors, ArithmeticFunction.moebius d : ℤ) : ℂ) := by push_cast; rfl
    rw [hcast, moebius_divisor_sum]
    split_ifs with hk1
    · rw [hk1]; simp [latticeWeightR]
    · simp
  simp_rw [hfibre]
  rw [tsum_eq_single 1]
  · simp
  · intro k hk
    rw [if_neg (fun h1 => hk (PNat.coe_eq_one_iff.mp h1))]

/-- The pointwise supremum leakage at the endpoint exponent b (HT1.9). No
b-moment of h is assumed. -/
theorem density_gap_leakage_sup {h : ℝ → ℂ} {H b : ℝ} (hb : 1 / 2 < b) (hcont : Continuous h)
    (heven : ∀ t, h (-t) = h t) (hdecay : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) :
    ENNReal.ofReal ((riemannZeta ((2 * b + 1 : ℝ) : ℂ) / riemannZeta ((b + 1 / 2 : ℝ) : ℂ)).re) *
        (⨆ t ∈ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (b * t) * ‖h t‖)) ≤
      ⨆ x ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (1 / 2 - b) * ‖mixtureDensity h x‖) := by
  have hs : 1 < b + 1 / 2 := by linarith
  set S := ∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(b + 1 / 2)) with hSdef
  have hS : 0 < S := tsum_abs_moebius_rpow_pos hs
  have hratio : (riemannZeta ((2 * b + 1 : ℝ) : ℂ) / riemannZeta ((b + 1 / 2 : ℝ) : ℂ)).re = S⁻¹ := by
    rw [← zeta_ratio_re hs]
    congr 3
    ring_nf
  rw [hratio]
  set G := ⨆ x ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (1 / 2 - b) * ‖mixtureDensity h x‖) with hGdef
  rcases eq_or_ne G ⊤ with hG | hG
  · rw [hG]; exact le_top
  set Gr := G.toReal with hGr
  have hGr0 : 0 ≤ Gr := ENNReal.toReal_nonneg
  -- Claim A: the lattice transform is bounded by e^(b y) Gr on y < 0
  have hA (y : ℝ) (hy : y < 0) : ‖latticeTransform h y‖ ≤ Real.exp (b * y) * Gr := by
    have hx : Real.exp y ∈ Ioo (0 : ℝ) 1 := ⟨Real.exp_pos y, Real.exp_lt_one_iff.mpr hy⟩
    have hle : ENNReal.ofReal ((Real.exp y) ^ (1 / 2 - b) * ‖mixtureDensity h (Real.exp y)‖) ≤ G :=
      le_iSup₂ (f := fun x (_ : x ∈ Ioo (0 : ℝ) 1) =>
        ENNReal.ofReal (x ^ (1 / 2 - b) * ‖mixtureDensity h x‖)) (Real.exp y) hx
    have hle' : (Real.exp y) ^ (1 / 2 - b) * ‖mixtureDensity h (Real.exp y)‖ ≤ Gr :=
      (ENNReal.ofReal_le_iff_le_toReal hG).mp hle
    rw [← mixtureDensity_exp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hpow : (Real.exp y) ^ (1 / 2 - b) = Real.exp ((1 / 2 - b) * y) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp, mul_comm]
    rw [hpow] at hle'
    calc Real.exp (y / 2) * ‖mixtureDensity h (Real.exp y)‖ =
        Real.exp (b * y) * (Real.exp ((1 / 2 - b) * y) * ‖mixtureDensity h (Real.exp y)‖) := by
          rw [← mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (b * y) * Gr := mul_le_mul_of_nonneg_left hle' (Real.exp_pos _).le
  -- Claim B: e^(-b y) ‖h y‖ ≤ S Gr on y < 0
  have hB (y : ℝ) (hy : y < 0) : Real.exp (-b * y) * ‖h y‖ ≤ S * Gr := by
    have hinv := latticeTransform_moebius_inverse hb hdecay hy.le
    have hterm (m : ℕ) : ‖((ArithmeticFunction.moebius m : ℝ) : ℂ) * (latticeWeightR m : ℂ) *
        latticeTransform h (y - Real.log m)‖ ≤
        (Real.exp (b * y) * Gr) * ((|ArithmeticFunction.moebius m| : ℝ) * (m : ℝ) ^ (-(b + 1 / 2))) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [latticeWeightR]
      have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
      have hAm := hA (y - Real.log m) (by linarith)
      have hw := latticeWeightR_rpow (by linarith : 0 < b + 1 / 2) m
      have hexp : Real.exp (b * (y - Real.log m)) = Real.exp (b * y) * Real.exp (-b * Real.log m) := by
        rw [← Real.exp_add]; ring_nf
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (latticeWeightR_nonneg m)]
      calc |(ArithmeticFunction.moebius m : ℝ)| * latticeWeightR m *
            ‖latticeTransform h (y - Real.log m)‖ ≤
          |(ArithmeticFunction.moebius m : ℝ)| * latticeWeightR m *
            (Real.exp (b * (y - Real.log m)) * Gr) :=
            mul_le_mul_of_nonneg_left hAm (mul_nonneg (abs_nonneg _) (latticeWeightR_nonneg m))
        _ = (Real.exp (b * y) * Gr) * (|(ArithmeticFunction.moebius m : ℝ)| *
            (latticeWeightR m * Real.exp (-b * Real.log m))) := by rw [hexp]; ring
        _ = _ := by rw [hw]
    have hsumB : Summable (fun m : ℕ =>
        (Real.exp (b * y) * Gr) * ((|ArithmeticFunction.moebius m| : ℝ) * (m : ℝ) ^ (-(b + 1 / 2)))) := by
      refine Summable.mul_left _ ?_
      refine (summable_nat_rpow_neg hs).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      have h' : (|ArithmeticFunction.moebius n| : ℝ) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc _ ≤ 1 * (n : ℝ) ^ (-(b + 1 / 2)) := mul_le_mul_of_nonneg_right h' (by positivity)
        _ = _ := one_mul _
    have hnorm : ‖h y‖ ≤ (Real.exp (b * y) * Gr) * S := by
      rw [← hinv, hSdef, ← tsum_mul_left]
      exact (norm_tsum_le_tsum_norm (hsumB.of_norm_bounded hterm |>.norm)).trans
        (hsumB.of_norm_bounded hterm |>.norm.tsum_le_tsum hterm hsumB) |>.trans_eq rfl
    calc Real.exp (-b * y) * ‖h y‖ ≤ Real.exp (-b * y) * ((Real.exp (b * y) * Gr) * S) :=
          mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
      _ = S * Gr := by
          rw [show Real.exp (-b * y) * (Real.exp (b * y) * Gr * S) =
            (Real.exp (-b * y) * Real.exp (b * y)) * (S * Gr) by ring, ← Real.exp_add]
          simp
  -- Claim C: e^(b t) ‖h t‖ ≤ S Gr for t ≥ 0
  have hC (t : ℝ) (ht : 0 ≤ t) : Real.exp (b * t) * ‖h t‖ ≤ S * Gr := by
    have hpos (t : ℝ) (ht : 0 < t) : Real.exp (b * t) * ‖h t‖ ≤ S * Gr := by
      have := hB (-t) (by linarith)
      rwa [heven, neg_mul_neg] at this
    rcases ht.lt_or_eq with ht | rfl
    · exact hpos t ht
    · have hcf : Continuous (fun t => Real.exp (b * t) * ‖h t‖) := by fun_prop
      have hlim : Tendsto (fun t => Real.exp (b * t) * ‖h t‖) (𝓝[>] 0)
          (𝓝 (Real.exp (b * 0) * ‖h 0‖)) := (hcf.tendsto 0).mono_left nhdsWithin_le_nhds
      exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun t ht => hpos t ht))
  have hsup : (⨆ t ∈ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (b * t) * ‖h t‖)) ≤
      ENNReal.ofReal S * G := by
    refine iSup₂_le (fun t ht => ?_)
    rw [← ENNReal.ofReal_toReal hG, ← ENNReal.ofReal_mul hS.le]
    exact ENNReal.ofReal_le_ofReal (hC t ht)
  calc ENNReal.ofReal S⁻¹ * (⨆ t ∈ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (b * t) * ‖h t‖)) ≤
      ENNReal.ofReal S⁻¹ * (ENNReal.ofReal S * G) := mul_le_mul le_rfl hsup zero_le zero_le
    _ = G := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hS.le), inv_mul_cancel₀ hS.ne',
        ENNReal.ofReal_one, one_mul]

/-! ### Endpoint distinction and the leakage root -/

lemma exp_neg_abs_le_inv_one_add_sq {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Real.exp (-c * |t|) ≤ (1 + 2 / c ^ 2) * (1 + t ^ 2)⁻¹ := by
  have hx : 0 ≤ c * |t| := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hexp : Real.exp (-c * |t|) * Real.exp (c * |t|) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE : 0 < Real.exp (c * |t|) := Real.exp_pos _
  rw [le_mul_inv_iff₀ (by positivity)]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have h1 : Real.exp (-c * |t|) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg t]
  have h2 : Real.exp (-c * |t|) * t ^ 2 ≤ 2 / c ^ 2 := by
    rw [le_div_iff₀ (by positivity), ht2]
    have hpos : 0 < Real.exp (-c * |t|) := Real.exp_pos _
    calc Real.exp (-c * |t|) * |t| ^ 2 * c ^ 2 =
        2 * (Real.exp (-c * |t|) * ((c * |t|) ^ 2 / 2)) := by ring
      _ ≤ 2 * (Real.exp (-c * |t|) * Real.exp (c * |t|)) := by
          gcongr; linarith [hq, hx]
      _ = 2 := by rw [hexp, mul_one]
  nlinarith

lemma lintegral_exp_mul_abs_decay_lt_top {h : ℝ → ℂ} {H a b : ℝ} (hab : a < b)
    (hdecay : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (a * |t|) * ‖h t‖) < ∞ := by
  have hc : 0 < b - a := by linarith
  have hint : Integrable (fun t : ℝ => (|H| * (1 + 2 / (b - a) ^ 2)) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine lt_of_le_of_lt (lintegral_mono (fun t => ENNReal.ofReal_le_ofReal ?_))
    hint.lintegral_lt_top
  calc Real.exp (a * |t|) * ‖h t‖ ≤ Real.exp (a * |t|) * (H * Real.exp (-b * |t|)) :=
        mul_le_mul_of_nonneg_left (hdecay t) (Real.exp_pos _).le
    _ = H * Real.exp (-(b - a) * |t|) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ |H| * Real.exp (-(b - a) * |t|) :=
        mul_le_mul_of_nonneg_right (le_abs_self H) (Real.exp_pos _).le
    _ ≤ |H| * ((1 + 2 / (b - a) ^ 2) * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (exp_neg_abs_le_inv_one_add_sq hc t) (abs_nonneg _)
    _ = _ := by ring

lemma endpoint_density_witness (b : ℝ) :
    let h : ℝ → ℂ := fun t => ((Real.exp (-b * |t|) : ℝ) : ℂ)
    Continuous h ∧ (∀ t, h (-t) = h t) ∧ (∀ t, ‖h t‖ ≤ 1 * Real.exp (-b * |t|)) ∧
      ∫⁻ t, ENNReal.ofReal (Real.exp (b * |t|) * ‖h t‖) = ∞ := by
  intro h
  refine ⟨by fun_prop, fun t => by simp [h, abs_neg], fun t => ?_, ?_⟩
  · show ‖((Real.exp (-b * |t|) : ℝ) : ℂ)‖ ≤ 1 * Real.exp (-b * |t|)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  · have hone (t : ℝ) : Real.exp (b * |t|) * ‖h t‖ = 1 := by
      simp only [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    simp only [hone, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact Real.volume_univ

/-! ### Positive-axis density of the actual mixture -/

/-- The coordinate density x^(-1/2) Σ_n n^(-1/2) g(log(x/n)) of a positive density g. -/
def positiveMixtureDensity (g : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt x)⁻¹ * ∑' n : ℕ, latticeWeight n * g (Real.log (x / n))

lemma dilatedCombMeasure_apply_pos (t : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hpos : s ⊆ Ioi 0) :
    dilatedCombMeasure t s =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (t / 2)) * s.indicator 1 (Real.exp t * n) := by
  rw [dilatedCombMeasure, Measure.smul_apply, smul_eq_mul, scaledLatticeMeasure,
    Measure.map_apply (scaledLatticePoint_measurable t) hs, ENNReal.tsum_mul_left]
  congr 1
  rw [← lintegral_indicator_one (MeasurableSet.of_discrete), lintegral_count]
  have hsupp : Function.support (fun n : ℤ => (scaledLatticePoint t ⁻¹' s).indicator
      (1 : ℤ → ℝ≥0∞) n) ⊆
      Set.range (Nat.cast : ℕ → ℤ) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hmem : scaledLatticePoint t n ∈ s := by
      by_contra h
      exact hn (Set.indicator_of_notMem (show n ∉ scaledLatticePoint t ⁻¹' s from h) _)
    have hp := hpos hmem
    simp only [scaledLatticePoint, Set.mem_Ioi] at hp
    have hn0 : (0 : ℝ) < n := by
      by_contra h
      push Not at h
      exact absurd hp (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos t).le h))
    exact ⟨n.toNat, by have : (0 : ℤ) < n := by exact_mod_cast hn0
                       omega⟩
  rw [← Nat.cast_injective.tsum_eq hsupp]
  rfl

/-- Change of variables x = e^t n along one lattice ray. -/
lemma lattice_ray_change_of_variables (g : ℝ → ℝ≥0∞) {n : ℕ} (hn : 0 < n) {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : s ⊆ Ioi 0) :
    ∫⁻ t, g t * (ENNReal.ofReal (Real.exp (t / 2)) * s.indicator 1 (Real.exp t * n)) =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt x)⁻¹ * (latticeWeight n * g (Real.log (x / n))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set F : ℝ → ℝ≥0∞ := s.indicator (fun x => ENNReal.ofReal (Real.sqrt x)⁻¹ *
    (latticeWeight n * g (Real.log (x / n)))) with hF
  have himage : (fun t : ℝ => Real.exp t * n) '' univ = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, -, rfl⟩
      exact mul_pos (Real.exp_pos t) hn'
    · intro hx
      refine ⟨Real.log (x / n), mem_univ _, ?_⟩
      show Real.exp (Real.log (x / n)) * n = x
      rw [Real.exp_log (div_pos hx hn')]
      field_simp
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (f := fun t : ℝ => Real.exp t * n) (f' := fun t => Real.exp t * n)
    (fun t _ => ((Real.hasDerivAt_exp t).mul_const (n : ℝ)).hasDerivWithinAt)
    (fun a _ b _ hab => Real.exp_injective (mul_right_cancel₀ hn'.ne' hab)) F
  rw [himage, Measure.restrict_univ] at hcv
  have hleft : ∫⁻ x in Ioi 0, F x = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt x)⁻¹ *
      (latticeWeight n * g (Real.log (x / n))) := by
    rw [hF, lintegral_indicator hs, Measure.restrict_restrict hs, Set.inter_eq_left.mpr hpos]
  rw [← hleft, hcv]
  refine lintegral_congr (fun t => ?_)
  by_cases hmem : Real.exp t * n ∈ s
  · rw [hF, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Pi.one_apply, mul_one,
      latticeWeight, if_neg hn.ne', abs_of_pos (mul_pos (Real.exp_pos t) hn')]
    have hlog : Real.log (Real.exp t * n / n) = t := by
      rw [mul_div_assoc, div_self hn'.ne', mul_one, Real.log_exp]
    rw [hlog]
    have hsq : Real.sqrt (Real.exp t * n) = Real.exp (t / 2) * Real.sqrt n := by
      rw [Real.sqrt_mul (Real.exp_pos t).le, Real.exp_half]
    have h1 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
    have h2 : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
    have h4 : 0 < Real.exp (t / 2) := Real.exp_pos _
    have hkey : Real.exp t * n * ((Real.sqrt (Real.exp t * n))⁻¹ * (Real.sqrt n)⁻¹) =
        Real.exp (t / 2) := by
      rw [hsq]
      calc Real.exp t * n * ((Real.exp (t / 2) * Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹) =
          (Real.exp (t / 2) * Real.exp (t / 2)) * (Real.sqrt n * Real.sqrt n) *
            ((Real.exp (t / 2) * Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹) := by rw [h2, h1]
        _ = Real.exp (t / 2) := by field_simp
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), mul_assoc (Real.exp t * n), hkey, mul_comm]
  · rw [hF, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero, mul_zero,
      mul_zero]

/-- The actual mixture of a positive density g is given on (0,∞) by the explicit
coordinate density (HT1.8, positive coordinate form). -/
theorem positiveDilationMixture_withDensity_apply {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {s : Set ℝ} (hs : MeasurableSet s) (hpos : s ⊆ Ioi 0) :
    positiveDilationMixture (volume.withDensity g) s = ∫⁻ x in s, positiveMixtureDensity g x := by
  have hind (n : ℕ) : Measurable (fun t : ℝ => s.indicator (1 : ℝ → ℝ≥0∞) (Real.exp t * n)) :=
    (measurable_const.indicator hs).comp (by fun_prop)
  have hmeas : Measurable (fun t : ℝ => ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (t / 2)) * s.indicator 1 (Real.exp t * n)) :=
    Measurable.tsum (fun n => (by fun_prop : Measurable fun t : ℝ =>
      ENNReal.ofReal (Real.exp (t / 2))).mul (hind n))
  rw [positiveDilationMixture_apply _ s hs]
  rw [lintegral_congr (fun t => dilatedCombMeasure_apply_pos t hs hpos),
    lintegral_withDensity_eq_lintegral_mul _ hg hmeas]
  simp only [Pi.mul_apply]
  simp_rw [← ENNReal.tsum_mul_left]
  refine (lintegral_tsum (fun n => ?_)).trans ?_
  · exact (hg.mul ((by fun_prop : Measurable fun t : ℝ =>
      ENNReal.ofReal (Real.exp (t / 2))).mul (hind n))).aemeasurable
  unfold positiveMixtureDensity
  simp_rw [← ENNReal.tsum_mul_left]
  refine Eq.trans ?_ (lintegral_tsum (fun n => ?_)).symm
  rotate_left
  · exact ((by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.sqrt x)⁻¹).mul
      (measurable_const.mul (hg.comp (by fun_prop)))).aemeasurable
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℝ) ∉ s := fun h => lt_irrefl (0 : ℝ) (hpos h)
    simp [latticeWeight, Set.indicator_of_notMem h0]
  · exact lattice_ray_change_of_variables g hn hs hpos

/-- The actual complex mixer h(t) dt of a continuous density, with its canonical
Jordan pairs (Re h)^± dt and (Im h)^± dt. -/
def densityMixer (h : ℝ → ℂ) (hc : Continuous h) : LocallyFiniteComplexMeasure where
  rePart :=
    { positive := volume.withDensity (fun t => ENNReal.ofReal (h t).re)
      negative := volume.withDensity (fun t => ENNReal.ofReal (-(h t).re))
      positive_locallyFinite := IsLocallyFiniteMeasure.withDensity_ofReal
        (Complex.continuous_re.comp hc)
      negative_locallyFinite := IsLocallyFiniteMeasure.withDensity_ofReal
        (Complex.continuous_re.comp hc).neg
      mutuallySingular := withDensity_ofReal_mutuallySingular
        (Complex.continuous_re.comp hc).measurable }
  imPart :=
    { positive := volume.withDensity (fun t => ENNReal.ofReal (h t).im)
      negative := volume.withDensity (fun t => ENNReal.ofReal (-(h t).im))
      positive_locallyFinite := IsLocallyFiniteMeasure.withDensity_ofReal
        (Complex.continuous_im.comp hc)
      negative_locallyFinite := IsLocallyFiniteMeasure.withDensity_ofReal
        (Complex.continuous_im.comp hc).neg
      mutuallySingular := withDensity_ofReal_mutuallySingular
        (Complex.continuous_im.comp hc).measurable }

/-- The four real coordinate functions Re⁺, Re⁻, Im⁺, Im⁻ (before positive parts). -/
def densityCoordinate (h : ℝ → ℂ) (i : Fin 4) (t : ℝ) : ℝ :=
  if i = 0 then (h t).re else if i = 1 then -(h t).re else if i = 2 then (h t).im else -(h t).im

@[simp] lemma densityCoordinate_zero (h : ℝ → ℂ) (t : ℝ) : densityCoordinate h 0 t = (h t).re := by
  simp [densityCoordinate]

@[simp] lemma densityCoordinate_one (h : ℝ → ℂ) (t : ℝ) : densityCoordinate h 1 t = -(h t).re := by
  simp [densityCoordinate]

@[simp] lemma densityCoordinate_two (h : ℝ → ℂ) (t : ℝ) : densityCoordinate h 2 t = (h t).im := by
  simp [densityCoordinate]

@[simp] lemma densityCoordinate_three (h : ℝ → ℂ) (t : ℝ) :
    densityCoordinate h 3 t = -(h t).im := by
  simp [densityCoordinate]

lemma mixingCoordinate_densityMixer (h : ℝ → ℂ) (hc : Continuous h) (i : Fin 4) :
    mixingCoordinate (densityMixer h hc) i =
      volume.withDensity (fun t => ENNReal.ofReal (densityCoordinate h i t)) := by
  fin_cases i <;> rfl

lemma densityCoordinate_measurable (h : ℝ → ℂ) (hc : Continuous h) (i : Fin 4) :
    Measurable (densityCoordinate h i) := by
  have hre := (Complex.continuous_re.comp hc).measurable
  have him := (Complex.continuous_im.comp hc).measurable
  fin_cases i
  · exact hre
  · exact hre.neg
  · exact him
  · exact him.neg

lemma norm_densityCoordinate_le (h : ℝ → ℂ) (i : Fin 4) (t : ℝ) :
    |densityCoordinate h i t| ≤ ‖h t‖ := by
  fin_cases i
  · exact Complex.abs_re_le_norm _
  · simpa [densityCoordinate] using Complex.abs_re_le_norm (h t)
  · exact Complex.abs_im_le_norm _
  · simpa [densityCoordinate] using Complex.abs_im_le_norm (h t)

/-- The density mixer lies in every exponential class below its decay rate. -/
lemma densityMixer_moment {h : ℝ → ℂ} (hc : Continuous h) {H a b : ℝ} (hab : a < b)
    (hdecay : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) :
    mixingExponentialMoment a (densityMixer h hc) < ∞ := by
  have hfin := lintegral_exp_mul_abs_decay_lt_top hab hdecay
  have hcoord (i : Fin 4) : ∫⁻ t, ENNReal.ofReal (Real.exp (a * |t|))
      ∂(mixingCoordinate (densityMixer h hc) i) < ∞ := by
    rw [mixingCoordinate_densityMixer, lintegral_withDensity_eq_lintegral_mul _
      (densityCoordinate_measurable h hc i).ennreal_ofReal (by fun_prop)]
    refine lt_of_le_of_lt (lintegral_mono (fun t => ?_)) hfin
    simp only [Pi.mul_apply]
    rw [mul_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (norm_densityCoordinate_le h i t)) (Real.exp_pos _).le)
  refine lt_of_le_of_lt (lintegral_mono' (LocallyFiniteComplexMeasure.totalVariation_le_control _)
    le_rfl) ?_
  have hsplit : (densityMixer h hc).variationControl =
      ((mixingCoordinate (densityMixer h hc) 0 + mixingCoordinate (densityMixer h hc) 1) +
        (mixingCoordinate (densityMixer h hc) 2 + mixingCoordinate (densityMixer h hc) 3)) := rfl
  rw [hsplit, lintegral_add_measure, lintegral_add_measure, lintegral_add_measure]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hcoord 0, hcoord 1⟩,
    ENNReal.add_lt_top.mpr ⟨hcoord 2, hcoord 3⟩⟩

lemma latticeWeight_eq_ofReal (n : ℕ) : latticeWeight n = ENNReal.ofReal (latticeWeightR n) := by
  unfold latticeWeight latticeWeightR
  split_ifs <;> simp

lemma mixtureDensity_summable {h : ℝ → ℂ} {H b : ℝ} (hb : 1 / 2 < b)
    (hdecay : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => latticeWeightR n * ‖h (Real.log (x / n))‖) := by
  have hH : 0 ≤ H := by
    have := (norm_nonneg _).trans (hdecay 0)
    simpa using this
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (latticeWeightR_nonneg n) (norm_nonneg _))
    (fun n => ?_) ((summable_nat_rpow_neg (by linarith : 1 < b + 1 / 2)).mul_left
      (H * Real.exp (b * Real.log x)))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show latticeWeightR 0 = 0 by simp [latticeWeightR], zero_mul]
    exact mul_nonneg (mul_nonneg hH (Real.exp_pos _).le) (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hlog : Real.log (x / n) = Real.log x - Real.log n := Real.log_div hx.ne' hn'.ne'
    have hb0 : 0 ≤ b := by linarith
    have h1 : ‖h (Real.log (x / n))‖ ≤ H * Real.exp (-b * (Real.log n - Real.log x)) := by
      refine (hdecay _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hH)
      rw [hlog, abs_sub_comm]
      nlinarith [le_abs_self (Real.log n - Real.log x)]
    calc latticeWeightR n * ‖h (Real.log (x / n))‖
        ≤ latticeWeightR n * (H * Real.exp (-b * (Real.log n - Real.log x))) :=
          mul_le_mul_of_nonneg_left h1 (latticeWeightR_nonneg n)
      _ = H * Real.exp (b * Real.log x) * (latticeWeightR n * Real.exp (-b * Real.log n)) := by
          rw [show -b * (Real.log n - Real.log x) = b * Real.log x + -b * Real.log n by ring,
            Real.exp_add]
          ring
      _ = H * Real.exp (b * Real.log x) * (n : ℝ) ^ (-(b + 1 / 2)) := by
          rw [latticeWeightR_rpow (by linarith) n]

/-- toReal of a coordinate density as a real series. -/
lemma positiveMixtureDensity_toReal {f : ℝ → ℝ} {x : ℝ}
    (hs : Summable (fun n : ℕ => latticeWeightR n * |f (Real.log (x / n))|)) :
    (positiveMixtureDensity (fun t => ENNReal.ofReal (f t)) x).toReal =
      (Real.sqrt x)⁻¹ * ∑' n : ℕ, latticeWeightR n * max (f (Real.log (x / n))) 0 := by
  have hterm (n : ℕ) : latticeWeight n * ENNReal.ofReal (f (Real.log (x / n))) =
      ENNReal.ofReal (latticeWeightR n * max (f (Real.log (x / n))) 0) := by
    rcases le_total (f (Real.log (x / n))) 0 with h0 | h0
    · rw [ENNReal.ofReal_of_nonpos h0, mul_zero, max_eq_right h0, mul_zero, ENNReal.ofReal_zero]
    · rw [max_eq_left h0, latticeWeight_eq_ofReal,
        ENNReal.ofReal_mul (latticeWeightR_nonneg n)]
  have hnn (n : ℕ) : 0 ≤ latticeWeightR n * max (f (Real.log (x / n))) 0 :=
    mul_nonneg (latticeWeightR_nonneg n) (le_max_right _ _)
  have hsum : Summable (fun n : ℕ => latticeWeightR n * max (f (Real.log (x / n))) 0) :=
    hs.of_nonneg_of_le hnn (fun n => mul_le_mul_of_nonneg_left
      (max_le (le_abs_self _) (abs_nonneg _)) (latticeWeightR_nonneg n))
  unfold positiveMixtureDensity
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Real.sqrt_nonneg x)),
    ENNReal.toReal_ofReal (tsum_nonneg hnn)]

lemma positiveMixtureDensity_lt_top {f : ℝ → ℝ} {x : ℝ}
    (hs : Summable (fun n : ℕ => latticeWeightR n * |f (Real.log (x / n))|)) :
    positiveMixtureDensity (fun t => ENNReal.ofReal (f t)) x < ∞ := by
  have hterm (n : ℕ) : latticeWeight n * ENNReal.ofReal (f (Real.log (x / n))) ≤
      ENNReal.ofReal (latticeWeightR n * |f (Real.log (x / n))|) := by
    rw [latticeWeight_eq_ofReal, ← ENNReal.ofReal_mul (latticeWeightR_nonneg n)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_abs_self _)
      (latticeWeightR_nonneg n))
  unfold positiveMixtureDensity
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (latticeWeightR_nonneg n)
    (abs_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

/-- The actual mixture of h(t) dt has positive-axis density r_h (HT1.8): its four coordinate
mixtures have the explicit densities D_i on (0,∞), each finite, and
r_h = (D_0 - D_1) + i (D_2 - D_3) pointwise. -/
theorem densityMixer_mixture_density {h : ℝ → ℂ} (hc : Continuous h) {H b : ℝ} (hb : 1 / 2 < b)
    (hdecay : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) :
    (∀ i : Fin 4, ∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioi 0 →
      positiveDilationMixture (mixingCoordinate (densityMixer h hc) i) s =
        ∫⁻ x in s, positiveMixtureDensity
          (fun t => ENNReal.ofReal (densityCoordinate h i t)) x) ∧
    (∀ i : Fin 4, ∀ x : ℝ, 0 < x →
      positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h i t)) x < ∞) ∧
    (∀ x : ℝ, 0 < x → mixtureDensity h x =
      (((positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 0 t)) x).toReal -
        (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 1 t)) x).toReal :
          ℝ) : ℂ) +
      Complex.I * (((positiveMixtureDensity
          (fun t => ENNReal.ofReal (densityCoordinate h 2 t)) x).toReal -
        (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 3 t)) x).toReal :
          ℝ) : ℂ)) := by
  have hcoordsum (i : Fin 4) {x : ℝ} (hx : 0 < x) :
      Summable (fun n : ℕ => latticeWeightR n * |densityCoordinate h i (Real.log (x / n))|) :=
    (mixtureDensity_summable hb hdecay hx).of_nonneg_of_le
      (fun n => mul_nonneg (latticeWeightR_nonneg n) (abs_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (norm_densityCoordinate_le h i _)
        (latticeWeightR_nonneg n))
  refine ⟨fun i s hs hpos => ?_, fun i x hx => positiveMixtureDensity_lt_top (hcoordsum i hx),
    fun x hx => ?_⟩
  · rw [mixingCoordinate_densityMixer]
    exact positiveDilationMixture_withDensity_apply
      (densityCoordinate_measurable h hc i).ennreal_ofReal hs hpos
  · rw [positiveMixtureDensity_toReal (hcoordsum 0 hx), positiveMixtureDensity_toReal (hcoordsum 1 hx),
      positiveMixtureDensity_toReal (hcoordsum 2 hx), positiveMixtureDensity_toReal (hcoordsum 3 hx)]
    have hS (i : Fin 4) : Summable (fun n : ℕ => latticeWeightR n *
        max (densityCoordinate h i (Real.log (x / n))) 0) :=
      (hcoordsum i hx).of_nonneg_of_le
        (fun n => mul_nonneg (latticeWeightR_nonneg n) (le_max_right _ _))
        (fun n => mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
          (latticeWeightR_nonneg n))
    have hre : (∑' n : ℕ, latticeWeightR n * max (densityCoordinate h 0 (Real.log (x / n))) 0) -
        ∑' n : ℕ, latticeWeightR n * max (densityCoordinate h 1 (Real.log (x / n))) 0 =
        ∑' n : ℕ, latticeWeightR n * (h (Real.log (x / n))).re := by
      rw [← (hS 0).tsum_sub (hS 1)]
      refine tsum_congr (fun n => ?_)
      rw [densityCoordinate_zero, densityCoordinate_one, ← mul_sub,
        max_zero_sub_max_neg_zero_eq_self]
    have him : (∑' n : ℕ, latticeWeightR n * max (densityCoordinate h 2 (Real.log (x / n))) 0) -
        ∑' n : ℕ, latticeWeightR n * max (densityCoordinate h 3 (Real.log (x / n))) 0 =
        ∑' n : ℕ, latticeWeightR n * (h (Real.log (x / n))).im := by
      rw [← (hS 2).tsum_sub (hS 3)]
      refine tsum_congr (fun n => ?_)
      rw [densityCoordinate_two, densityCoordinate_three, ← mul_sub,
        max_zero_sub_max_neg_zero_eq_self]
    have hTsum : Summable (fun n : ℕ => (latticeWeightR n : ℂ) * h (Real.log (x / n))) := by
      refine Summable.of_norm ?_
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (latticeWeightR_nonneg _)] using mixtureDensity_summable hb hdecay hx
    obtain ⟨h1, h2⟩ := (Complex.hasSum_iff _ _).mp hTsum.hasSum
    have hTre : (∑' n : ℕ, (latticeWeightR n : ℂ) * h (Real.log (x / n))).re =
        ∑' n : ℕ, latticeWeightR n * (h (Real.log (x / n))).re := by
      rw [← h1.tsum_eq]
      exact tsum_congr (fun n => Complex.re_ofReal_mul _ _)
    have hTim : (∑' n : ℕ, (latticeWeightR n : ℂ) * h (Real.log (x / n))).im =
        ∑' n : ℕ, latticeWeightR n * (h (Real.log (x / n))).im := by
      rw [← h2.tsum_eq]
      exact tsum_congr (fun n => Complex.im_ofReal_mul _ _)
    rw [← mul_sub, ← mul_sub, hre, him]
    unfold mixtureDensity
    apply Complex.ext
    · simp [Complex.mul_re, hTre]
    · simp [Complex.mul_im, hTim]


/-! ### Exact leakage with genuine complex variations (HT1.7) -/

/-- A real rotation of a finite complex measure has no larger variation. -/
lemma complexMeasure_rotation_variation_le (c : ComplexMeasure ℝ) {α β : ℝ}
    (hαβ : α ^ 2 + β ^ 2 ≤ 1) :
    (α • ComplexMeasure.re c + β • ComplexMeasure.im c).variation ≤ c.variation := by
  refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
  refine le_trans ?_ (VectorMeasure.enorm_measure_le_variation c E)
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [add_apply, smul_apply, ComplexMeasure.re_apply,
    ComplexMeasure.im_apply, smul_eq_mul, Real.norm_eq_abs]
  have hz : ‖c E‖ ^ 2 = (c E).re ^ 2 + (c E).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : (α * (c E).re + β * (c E).im) ^ 2 ≤ ‖c E‖ ^ 2 := by
    rw [hz]
    nlinarith [sq_nonneg (α * (c E).im - β * (c E).re), sq_nonneg (c E).re, sq_nonneg (c E).im]
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (norm_nonneg _))

/-- Real integral against a compact Jordan restriction. -/
lemma localSignedCompactRestriction_integral_real (μ : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    {K : Set ℝ} (hK : IsCompact K) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (hsupp : ∀ x ∉ K, g x = 0) :
    ∫ᵛ x, g x ∂<•localSignedCompactRestriction μ K hK =
      (∫ x, g x ∂μ.positive) - ∫ x, g x ∂μ.negative := by
  have : IsFiniteMeasure (μ.positive.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have : IsFiniteMeasure (μ.negative.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hp : (μ.positive.restrict K).toSignedMeasure.Integrable g := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hgC)
  have hn : (μ.negative.restrict K).toSignedMeasure.Integrable g := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hgC)
  rw [localSignedCompactRestriction, VectorMeasure.integral_sub_vectorMeasure hp hn,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]

/-- Exact complex integral bound for a nonnegative real weight: the complex number
∫ g dν (assembled from the Jordan parts) has modulus at most ∫ g d|ν|, with |ν| the genuine
complex variation. -/
lemma complexIntegral_real_norm_le (μ : LocallyFiniteComplexMeasure) {K : Set ℝ}
    (hK : IsCompact K) {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C : ℝ}
    (hgC : ∀ x, g x ≤ C) (hsupp : ∀ x ∉ K, g x = 0) :
    ENNReal.ofReal ‖((((∫ x, g x ∂μ.rePart.positive) - ∫ x, g x ∂μ.rePart.negative : ℝ)) : ℂ) +
        I * ((((∫ x, g x ∂μ.imPart.positive) - ∫ x, g x ∂μ.imPart.negative : ℝ)) : ℂ)‖ ≤
      ∫⁻ x, ENNReal.ofReal (g x) ∂μ.totalVariation := by
  set c := μ.compactRestriction K hK with hc
  have hgC' : ∀ x, |g x| ≤ C := fun x => by rw [abs_of_nonneg (hg0 x)]; exact hgC x
  set A : ℝ := (∫ x, g x ∂μ.rePart.positive) - ∫ x, g x ∂μ.rePart.negative with hA
  set B : ℝ := (∫ x, g x ∂μ.imPart.positive) - ∫ x, g x ∂μ.imPart.negative with hB
  have hcA : ∫ᵛ x, g x ∂<•(ComplexMeasure.re c) = A := by
    rw [hc, LocallyFiniteComplexMeasure.compactRestriction_re]
    exact localSignedCompactRestriction_integral_real _ hK hg hgC' hsupp
  have hcB : ∫ᵛ x, g x ∂<•(ComplexMeasure.im c) = B := by
    rw [hc, LocallyFiniteComplexMeasure.compactRestriction_im]
    exact localSignedCompactRestriction_integral_real _ hK hg hgC' hsupp
  set z : ℂ := (A : ℂ) + I * (B : ℂ) with hz
  have hzre : z.re = A := by simp [hz]
  have hzim : z.im = B := by simp [hz]
  by_cases hz0 : z = 0
  · rw [hz0, norm_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hnormsq : ‖z‖ ^ 2 = A ^ 2 + B ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]; ring
  set α : ℝ := A / ‖z‖ with hα
  set β : ℝ := B / ‖z‖ with hβ
  have hαβ : α ^ 2 + β ^ 2 ≤ 1 := by
    rw [hα, hβ, div_pow, div_pow, ← add_div, ← hnormsq, div_self (by positivity)]
  set ρ : SignedMeasure ℝ := α • ComplexMeasure.re c + β • ComplexMeasure.im c with hρ
  have hfinre : IsFiniteMeasure (ComplexMeasure.re c).variation := inferInstance
  have hfinim : IsFiniteMeasure (ComplexMeasure.im c).variation := inferInstance
  have hire : (ComplexMeasure.re c).Integrable g :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hgC')
  have hiim : (ComplexMeasure.im c).Integrable g :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hgC')
  have hint : ∫ᵛ x, g x ∂<•ρ = ‖z‖ := by
    rw [hρ, VectorMeasure.integral_add_vectorMeasure (hire.smul_vectorMeasure α)
      (hiim.smul_vectorMeasure β), VectorMeasure.integral_smul_vectorMeasure,
      VectorMeasure.integral_smul_vectorMeasure, hcA, hcB, smul_eq_mul, smul_eq_mul, hα, hβ]
    field_simp
    rw [← hnormsq]
  have hbound := VectorMeasure.enorm_integral_le_lintegral_enorm_transpose
    (μ := ρ) (f := g) (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
  rw [VectorMeasure.variation_transpose_lsmul_flip, hint] at hbound
  calc ENNReal.ofReal ‖z‖ = ‖(‖z‖ : ℝ)‖ₑ := by rw [Real.enorm_eq_ofReal (norm_nonneg _)]
    _ ≤ ∫⁻ x, ‖g x‖ₑ ∂ρ.variation := hbound
    _ = ∫⁻ x, ENNReal.ofReal (g x) ∂ρ.variation :=
        lintegral_congr (fun x => Real.enorm_eq_ofReal (hg0 x))
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂c.variation :=
        lintegral_mono' (complexMeasure_rotation_variation_le c hαβ) le_rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ.totalVariation :=
        lintegral_mono' (μ.compactRestriction_variation_le_totalVariation K hK) le_rfl

/-- The weighted logarithmic transport of a bounded negative-axis set, as a real weight. -/
lemma positiveLogMeasure_apply_eq_lintegral (m : Measure ℝ) {G : Set ℝ} (hG : MeasurableSet G) :
    positiveLogMeasure m G = ∫⁻ x, ENNReal.ofReal
      ((Ioi 0 ∩ Real.log ⁻¹' G).indicator (fun x => (Real.sqrt x)⁻¹) x) ∂m := by
  rw [← lintegral_indicator_one hG,
    lintegral_positiveLogMeasure m (f := G.indicator (1 : ℝ → ℝ≥0∞)) (measurable_one.indicator hG)]
  refine lintegral_congr (fun x => ?_)
  by_cases hx : 0 < x
  · by_cases hl : Real.log x ∈ G
    · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
        Set.indicator_of_mem (show x ∈ Ioi 0 ∩ Real.log ⁻¹' G from ⟨hx, hl⟩),
        Set.indicator_of_mem hl, Pi.one_apply, mul_one, positiveLogWeight, if_pos hx]
    · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
        Set.indicator_of_notMem (show x ∉ Ioi 0 ∩ Real.log ⁻¹' G from fun h => hl h.2),
        Set.indicator_of_notMem hl, mul_zero, ENNReal.ofReal_zero]
  · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
      Set.indicator_of_notMem (show x ∉ Ioi 0 ∩ Real.log ⁻¹' G from fun h => hx h.1),
      ENNReal.ofReal_zero]

/-- The log transport of the actual complex measure is dominated by the transport of its
genuine variation, on bounded sets of the closed negative axis. -/
lemma positiveLogMeasure_complex_bound (ν : LocallyFiniteComplexMeasure) {G : Set ℝ}
    (hG : MeasurableSet G) {R : ℝ} (hGR : G ⊆ Icc (-R) 0) :
    ENNReal.ofReal ‖((((positiveLogMeasure ν.rePart.positive G).toReal -
          (positiveLogMeasure ν.rePart.negative G).toReal : ℝ)) : ℂ) +
        I * ((((positiveLogMeasure ν.imPart.positive G).toReal -
          (positiveLogMeasure ν.imPart.negative G).toReal : ℝ)) : ℂ)‖ ≤
      positiveLogMeasure ν.totalVariation G := by
  set g : ℝ → ℝ := (Ioi 0 ∩ Real.log ⁻¹' G).indicator (fun x => (Real.sqrt x)⁻¹) with hgdef
  have hS : MeasurableSet (Ioi (0 : ℝ) ∩ Real.log ⁻¹' G) :=
    measurableSet_Ioi.inter (Real.measurable_log hG)
  have hgm : Measurable g := (by fun_prop : Measurable fun x : ℝ => (Real.sqrt x)⁻¹).indicator hS
  have hg0 : ∀ x, 0 ≤ g x := fun x => Set.indicator_nonneg (fun _ _ => by positivity) x
  have hmemK : ∀ x ∈ Ioi (0 : ℝ) ∩ Real.log ⁻¹' G, x ∈ Icc (Real.exp (-R)) 1 := by
    intro x hx
    have hl := hGR hx.2
    have hx0 : (0 : ℝ) < x := hx.1
    refine ⟨?_, ?_⟩
    · rw [← Real.exp_log hx0]; exact Real.exp_le_exp.mpr hl.1
    · rw [← Real.exp_log hx0, ← Real.exp_zero]; exact Real.exp_le_exp.mpr hl.2
  have hsupp : ∀ x ∉ Icc (Real.exp (-R)) 1, g x = 0 :=
    fun x hx => Set.indicator_of_notMem (fun h => hx (hmemK x h)) _
  have hgC : ∀ x, g x ≤ Real.exp (R / 2) := by
    intro x
    by_cases hx : x ∈ Ioi (0 : ℝ) ∩ Real.log ⁻¹' G
    · rw [hgdef, Set.indicator_of_mem hx]
      have hK := hmemK x hx
      have hsq : Real.exp (-R / 2) ≤ Real.sqrt x := by
        rw [show -R / 2 = (-R) / 2 by ring, Real.exp_half]
        exact Real.sqrt_le_sqrt hK.1
      rw [inv_le_comm₀ (Real.sqrt_pos.mpr hx.1) (Real.exp_pos _), ← Real.exp_neg]
      have h2 : -(R / 2) = -R / 2 := by ring
      rw [h2]
      exact hsq
    · rw [hgdef, Set.indicator_of_notMem hx]; exact (Real.exp_pos _).le
  have hval (m : Measure ℝ) : positiveLogMeasure m G = ∫⁻ x, ENNReal.ofReal (g x) ∂m :=
    positiveLogMeasure_apply_eq_lintegral m hG
  have hreal (m : Measure ℝ) : (positiveLogMeasure m G).toReal = ∫ x, g x ∂m := by
    rw [hval, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0)
      hgm.aestronglyMeasurable]
  rw [hreal, hreal, hreal, hreal, hval]
  exact complexIntegral_real_norm_le ν isCompact_Icc hgm hg0 hgC hsupp

/-- Real form of a lattice convolution value. -/
lemma latticeMeasure_conv_toReal (w : ℕ → ℝ≥0∞) (ρ : Measure ℝ) [SFinite ρ] {F : Set ℝ}
    (hF : MeasurableSet F) (hfin : (latticeMeasure w ∗ ρ) F ≠ ∞) :
    Summable (fun k : ℕ => (w k).toReal * (ρ ((fun y => Real.log k + y) ⁻¹' F)).toReal) ∧
    ((latticeMeasure w ∗ ρ) F).toReal =
      ∑' k : ℕ, (w k).toReal * (ρ ((fun y => Real.log k + y) ⁻¹' F)).toReal := by
  rw [latticeMeasure_conv_apply _ _ hF] at hfin ⊢
  have hterm (k : ℕ) := ENNReal.ne_top_of_tsum_ne_top hfin k
  refine ⟨?_, ?_⟩
  · simpa only [ENNReal.toReal_mul] using ENNReal.summable_toReal hfin
  · rw [ENNReal.tsum_toReal_eq hterm]
    simp only [ENNReal.toReal_mul]

lemma moebiusComb_add_eq_latticeMeasure :
    moebiusPlusComb + moebiusMinusComb = latticeMeasure (fun k =>
      (if ArithmeticFunction.moebius k = 1 then latticeWeight k else 0) +
      (if ArithmeticFunction.moebius k = -1 then latticeWeight k else 0)) := by
  unfold moebiusPlusComb moebiusMinusComb latticeMeasure
  rw [Measure.sum_add_sum]
  simp_rw [add_smul]

lemma latticeShift_subset {F : Set ℝ} {R : ℝ} (hFR : F ⊆ Icc (-R) 0) (k : ℕ) :
    (fun y => Real.log k + y) ⁻¹' F ⊆ Icc (-(R + Real.log k)) 0 := by
  intro y hy
  have h := hFR hy
  have hk : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  simp only [mem_Icc] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Causal Möbius expansion of a complex value on a bounded negative-axis set, bounded term by
term by a dominating measure V of the transported complex values. -/
lemma moebius_complex_value_bound
    {P Q P' Q' ηp ηn ξp ξn V : Measure ℝ} [SFinite ηp] [SFinite ηn] [SFinite ξp] [SFinite ξn]
    [SFinite V]
    (hre : P + (moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) =
      Q + (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn))
    (him : P' + (moebiusPlusComb ∗ ξn + moebiusMinusComb ∗ ξp) =
      Q' + (moebiusPlusComb ∗ ξp + moebiusMinusComb ∗ ξn))
    (hη : ∀ G : Set ℝ, MeasurableSet G → ∀ R' : ℝ, G ⊆ Icc (-R') 0 →
      ENNReal.ofReal ‖((((ηp G).toReal - (ηn G).toReal : ℝ)) : ℂ) +
        I * ((((ξp G).toReal - (ξn G).toReal : ℝ)) : ℂ)‖ ≤ V G)
    {F : Set ℝ} (hF : MeasurableSet F) {R : ℝ} (hFR : F ⊆ Icc (-R) 0)
    (hP : P F ≠ ∞) (hQ : Q F ≠ ∞) (hP' : P' F ≠ ∞) (hQ' : Q' F ≠ ∞)
    (h1 : (moebiusPlusComb ∗ ηp) F ≠ ∞) (h2 : (moebiusPlusComb ∗ ηn) F ≠ ∞)
    (h3 : (moebiusMinusComb ∗ ηp) F ≠ ∞) (h4 : (moebiusMinusComb ∗ ηn) F ≠ ∞)
    (h5 : (moebiusPlusComb ∗ ξp) F ≠ ∞) (h6 : (moebiusPlusComb ∗ ξn) F ≠ ∞)
    (h7 : (moebiusMinusComb ∗ ξp) F ≠ ∞) (h8 : (moebiusMinusComb ∗ ξn) F ≠ ∞) :
    ENNReal.ofReal ‖((((P F).toReal - (Q F).toReal : ℝ)) : ℂ) +
        I * ((((P' F).toReal - (Q' F).toReal : ℝ)) : ℂ)‖ ≤
      ((moebiusPlusComb + moebiusMinusComb) ∗ V) F := by
  set wp : ℕ → ℝ≥0∞ := fun k => if ArithmeticFunction.moebius k = 1 then latticeWeight k else 0
    with hwp
  set wm : ℕ → ℝ≥0∞ := fun k => if ArithmeticFunction.moebius k = -1 then latticeWeight k else 0
    with hwm
  have hMp : moebiusPlusComb = latticeMeasure wp := rfl
  have hMm : moebiusMinusComb = latticeMeasure wm := rfl
  set sh : ℕ → Set ℝ := fun k => (fun y => Real.log k + y) ⁻¹' F with hsh
  -- real forms of the eight lattice values
  obtain ⟨s1, e1⟩ := latticeMeasure_conv_toReal wp ηp hF (hMp ▸ h1)
  obtain ⟨s2, e2⟩ := latticeMeasure_conv_toReal wp ηn hF (hMp ▸ h2)
  obtain ⟨s3, e3⟩ := latticeMeasure_conv_toReal wm ηp hF (hMm ▸ h3)
  obtain ⟨s4, e4⟩ := latticeMeasure_conv_toReal wm ηn hF (hMm ▸ h4)
  obtain ⟨s5, e5⟩ := latticeMeasure_conv_toReal wp ξp hF (hMp ▸ h5)
  obtain ⟨s6, e6⟩ := latticeMeasure_conv_toReal wp ξn hF (hMp ▸ h6)
  obtain ⟨s7, e7⟩ := latticeMeasure_conv_toReal wm ξp hF (hMm ▸ h7)
  obtain ⟨s8, e8⟩ := latticeMeasure_conv_toReal wm ξn hF (hMm ▸ h8)
  -- the real Jordan identities at F
  have hreF := congrArg (fun m : Measure ℝ => (m F).toReal) hre
  have himF := congrArg (fun m : Measure ℝ => (m F).toReal) him
  simp only [Measure.add_apply] at hreF himF
  rw [ENNReal.toReal_add hP (ENNReal.add_ne_top.mpr ⟨h2, h3⟩), ENNReal.toReal_add h2 h3,
    ENNReal.toReal_add hQ (ENNReal.add_ne_top.mpr ⟨h1, h4⟩), ENNReal.toReal_add h1 h4] at hreF
  rw [ENNReal.toReal_add hP' (ENNReal.add_ne_top.mpr ⟨h6, h7⟩), ENNReal.toReal_add h6 h7,
    ENNReal.toReal_add hQ' (ENNReal.add_ne_top.mpr ⟨h5, h8⟩), ENNReal.toReal_add h5 h8] at himF
  rw [hMp, hMm] at hreF himF
  rw [e1, e2, e3, e4] at hreF
  rw [e5, e6, e7, e8] at himF
  set m : ℕ → ℝ := fun k => (wp k).toReal - (wm k).toReal with hm
  set u : ℕ → ℝ := fun k => (ηp (sh k)).toReal - (ηn (sh k)).toReal with hu
  set v : ℕ → ℝ := fun k => (ξp (sh k)).toReal - (ξn (sh k)).toReal with hv
  have hsu : Summable (fun k => m k * u k) := by
    have := ((s1.add s4).sub s2).sub s3
    refine this.congr (fun k => ?_)
    simp only [hm, hu, hsh]; ring
  have hsv : Summable (fun k => m k * v k) := by
    have := ((s5.add s8).sub s6).sub s7
    refine this.congr (fun k => ?_)
    simp only [hm, hv, hsh]; ring
  have hA : (P F).toReal - (Q F).toReal = ∑' k, m k * u k := by
    have hcomb : ∑' k, m k * u k = (∑' k, (wp k).toReal * (ηp (sh k)).toReal) +
        (∑' k, (wm k).toReal * (ηn (sh k)).toReal) -
        (∑' k, (wp k).toReal * (ηn (sh k)).toReal) -
        (∑' k, (wm k).toReal * (ηp (sh k)).toReal) := by
      rw [← s1.tsum_add s4, ← (s1.add s4).tsum_sub s2, ← ((s1.add s4).sub s2).tsum_sub s3]
      refine tsum_congr (fun k => ?_)
      simp only [hm, hu]; ring
    rw [hcomb]
    linarith
  have hB : (P' F).toReal - (Q' F).toReal = ∑' k, m k * v k := by
    have hcomb : ∑' k, m k * v k = (∑' k, (wp k).toReal * (ξp (sh k)).toReal) +
        (∑' k, (wm k).toReal * (ξn (sh k)).toReal) -
        (∑' k, (wp k).toReal * (ξn (sh k)).toReal) -
        (∑' k, (wm k).toReal * (ξp (sh k)).toReal) := by
      rw [← s5.tsum_add s8, ← (s5.add s8).tsum_sub s6, ← ((s5.add s8).sub s6).tsum_sub s7]
      refine tsum_congr (fun k => ?_)
      simp only [hm, hv]; ring
    rw [hcomb]
    linarith
  -- complex series
  set c : ℕ → ℂ := fun k => ((u k : ℝ) : ℂ) + I * ((v k : ℝ) : ℂ) with hc
  have hterm (k : ℕ) : ((m k * u k : ℝ) : ℂ) + I * ((m k * v k : ℝ) : ℂ) = (m k : ℂ) * c k := by
    simp only [hc]; push_cast; ring
  have hz : HasSum (fun k => (m k : ℂ) * c k)
      ((((P F).toReal - (Q F).toReal : ℝ) : ℂ) + I * (((P' F).toReal - (Q' F).toReal : ℝ) : ℂ)) := by
    rw [hA, hB]
    have h1' := (Complex.hasSum_ofReal.mpr hsu.hasSum)
    have h2' := (Complex.hasSum_ofReal.mpr hsv.hasSum).mul_left I
    exact (h1'.add h2').congr_fun (fun k => (hterm k).symm)
  have hnormc (k : ℕ) : ‖(m k : ℂ) * c k‖ ≤ |m k * u k| + |m k * v k| := by
    rw [← hterm k]
    refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul, abs_mul,
      le_refl]
  have hsn : Summable (fun k => ‖(m k : ℂ) * c k‖) :=
    (hsu.abs.add hsv.abs).of_nonneg_of_le (fun k => norm_nonneg _) hnormc
  rw [← hz.tsum_eq]
  refine le_trans (ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hsn)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => norm_nonneg _) hsn, moebiusComb_add_eq_latticeMeasure,
    latticeMeasure_conv_apply _ _ hF]
  refine ENNReal.tsum_le_tsum (fun k => ?_)
  have hwpf : wp k ≠ ∞ := by
    simp only [hwp, latticeWeight]; split_ifs <;> simp
  have hwmf : wm k ≠ ∞ := by
    simp only [hwm, latticeWeight]; split_ifs <;> simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg _)]
  refine mul_le_mul ?_ ?_ zero_le zero_le
  · have habs : |m k| ≤ (wp k).toReal + (wm k).toReal := by
      simp only [hm]
      rw [abs_le]
      constructor <;> linarith [ENNReal.toReal_nonneg (a := wp k), ENNReal.toReal_nonneg (a := wm k)]
    calc ENNReal.ofReal |m k| ≤ ENNReal.ofReal ((wp k).toReal + (wm k).toReal) :=
          ENNReal.ofReal_le_ofReal habs
      _ = wp k + wm k := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hwpf, ENNReal.ofReal_toReal hwmf]
  · exact hη (sh k) (measurable_const_add _ hF) (R + Real.log k) (latticeShift_subset hFR k)

lemma measure_le_weightedLogNorm (ρ : Measure ℝ) {a : ℝ} (ha : 0 ≤ a) {F : Set ℝ}
    (hF : MeasurableSet F) (hneg : F ⊆ Iic 0) : ρ F ≤ weightedLogNorm a ρ := by
  rw [← lintegral_indicator_one hF]
  refine lintegral_mono (fun t => ?_)
  by_cases ht : t ∈ F
  · rw [Set.indicator_of_mem ht, Pi.one_apply, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
    have : t ≤ 0 := hneg ht
    nlinarith
  · rw [Set.indicator_of_notMem ht]; exact zero_le

/-- Exact weighted gap leakage with the genuine complex variations |σ| and |ν| (HT1.7). -/
theorem complex_gap_leakage (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞) :
    ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture σ a ha.le hm).totalVariation := by
  have ha0 : 0 ≤ a := by linarith
  have hs : 1 < a + 1 / 2 := by linarith
  set ν := weightedDilationMixture σ a ha.le hm with hν
  set S := ∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) with hSdef
  have hS : 0 < S := tsum_abs_moebius_rpow_pos hs
  have hratio : (riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re = S⁻¹ := by
    rw [← zeta_ratio_re hs]; congr 3; ring_nf
  have hMnorm : weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) = ENNReal.ofReal S :=
    weightedLogNorm_moebiusComb ha
  obtain ⟨-, -, -, -, hinvre, hinvim, -, ⟨hηrp, hηrn, hηip, hηin⟩, -⟩ :=
    weighted_mobius_inverse σ a ha hm
  have hMp := (weightedLogNorm_moebiusComb_lt_top ha).1
  have hMm := (weightedLogNorm_moebiusComb_lt_top ha).2
  set W := positiveLogMeasure ν.totalVariation with hW
  set V₀ := W.restrict (Iio 0) with hV₀
  set Λ := (moebiusPlusComb + moebiusMinusComb) ∗ V₀ with hΛ
  -- finiteness of the eight lattice values on bounded negative sets
  have hconv {ρ : Measure ℝ} [SFinite ρ] (hρ : weightedLogNorm a ρ < ∞) {M : Measure ℝ}
      (hM : weightedLogNorm a M < ∞) {F : Set ℝ} (hF : MeasurableSet F) (hneg : F ⊆ Iic 0) :
      (M ∗ ρ) F ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_le_weightedLogNorm _ ha0 hF hneg)
    rw [weightedLogNorm_conv]
    exact ENNReal.mul_ne_top hM.ne hρ.ne
  -- the measure inequality on each compact window
  have hwindow (n : ℕ) (A : Set ℝ) (hA : MeasurableSet A) :
      σ.totalVariation (A ∩ Iio 0 ∩ localMeasureInterval n) ≤ Λ A := by
    set K := localMeasureInterval n with hK
    have hKc : IsCompact K := isCompact_Icc
    set c := σ.compactRestriction K hKc with hc
    have hvar : (c.restrict (Iio 0)).variation ≤ Λ := by
      refine VectorMeasure.variation_le_of_forall_enorm_le (fun E hE => ?_)
      set F := E ∩ Iio 0 ∩ K with hFdef
      have hFm : MeasurableSet F := (hE.inter measurableSet_Iio).inter hKc.measurableSet
      have hFR : F ⊆ Icc (-(n : ℝ)) 0 := fun y hy => ⟨hy.2.1, hy.1.2.le⟩
      have hFneg : F ⊆ Iic 0 := fun y hy => (show y < 0 from hy.1.2).le
      have hcE : (c.restrict (Iio 0)) E =
          (((σ.rePart.positive F).toReal - (σ.rePart.negative F).toReal : ℝ) : ℂ) +
            I * (((σ.imPart.positive F).toReal - (σ.imPart.negative F).toReal : ℝ) : ℂ) := by
        rw [VectorMeasure.restrict_apply _ measurableSet_Iio hE]
        apply Complex.ext
        · show (ComplexMeasure.re c) (E ∩ Iio 0) = _
          rw [hc, LocallyFiniteComplexMeasure.compactRestriction_re,
            localSignedCompactRestriction_apply _ _ hKc _ (hE.inter measurableSet_Iio)]
          simp [Measure.real, Measure.restrict_apply (hE.inter measurableSet_Iio), hFdef]
        · show (ComplexMeasure.im c) (E ∩ Iio 0) = _
          rw [hc, LocallyFiniteComplexMeasure.compactRestriction_im,
            localSignedCompactRestriction_apply _ _ hKc _ (hE.inter measurableSet_Iio)]
          simp [Measure.real, Measure.restrict_apply (hE.inter measurableSet_Iio), hFdef]
      rw [hcE, ← ofReal_norm]
      have hfinK (m : Measure ℝ) [IsLocallyFiniteMeasure m] : m F ≠ ∞ :=
        ne_top_of_le_ne_top (hKc.measure_lt_top.ne) (measure_mono inter_subset_right)
      have hbound := moebius_complex_value_bound (V := W) hinvre hinvim
        (fun G hG R' hGR => positiveLogMeasure_complex_bound ν hG hGR) hFm hFR
        (hfinK _) (hfinK _) (hfinK _) (hfinK _)
        (hconv hηrp hMp hFm hFneg) (hconv hηrn hMp hFm hFneg)
        (hconv hηrp hMm hFm hFneg) (hconv hηrn hMm hFm hFneg)
        (hconv hηip hMp hFm hFneg) (hconv hηin hMp hFm hFneg)
        (hconv hηip hMm hFm hFneg) (hconv hηin hMm hFm hFneg)
      refine hbound.trans ?_
      have hcaus := latticeMeasure_conv_restrict_Iio (fun k =>
        (if ArithmeticFunction.moebius k = 1 then latticeWeight k else 0) +
        (if ArithmeticFunction.moebius k = -1 then latticeWeight k else 0)) (by simp) W
      rw [← moebiusComb_add_eq_latticeMeasure] at hcaus
      calc ((moebiusPlusComb + moebiusMinusComb) ∗ W) F
          = (((moebiusPlusComb + moebiusMinusComb) ∗ W).restrict (Iio 0)) F := by
            rw [Measure.restrict_apply hFm, Set.inter_eq_left.mpr (fun y hy => hy.1.2)]
        _ ≤ Λ F := Measure.le_iff'.mp hcaus F
        _ ≤ Λ E := measure_mono (fun y hy => hy.1.1)
    rw [VectorMeasure.variation_restrict measurableSet_Iio, hc,
      ← LocallyFiniteComplexMeasure.totalVariation_restrict_compact] at hvar
    have := Measure.le_iff'.mp hvar A
    rw [Measure.restrict_apply hA, Measure.restrict_apply (hA.inter measurableSet_Iio)] at this
    exact this
  have hle : σ.totalVariation.restrict (Iio 0) ≤ Λ := by
    refine Measure.le_iff.mpr (fun A hA => ?_)
    rw [Measure.restrict_apply hA]
    have hU : A ∩ Iio 0 = ⋃ n : ℕ, A ∩ Iio 0 ∩ localMeasureInterval n := by
      rw [← Set.inter_iUnion, localMeasureInterval_cover, Set.inter_univ]
    have hmono : Monotone (fun n : ℕ => A ∩ Iio 0 ∩ localMeasureInterval n) := by
      intro i j hij x hx
      refine ⟨hx.1, ?_⟩
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      exact ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
    rw [hU, hmono.measure_iUnion]
    exact iSup_le (fun n => hwindow n A hA)
  -- integrate the weight
  have hint : ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation ≤
      ENNReal.ofReal S * ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2)) ∂ν.totalVariation := by
    calc ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation
        ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t)) ∂Λ := lintegral_mono' hle le_rfl
      _ = weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) * weightedLogNorm a V₀ :=
          weightedLogNorm_conv a _ _
      _ = _ := by
          rw [hMnorm, weightedLogNorm, hV₀, hW, setLIntegral_positiveLogMeasure_Iio]
  calc ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) /
        riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation
      ≤ ENNReal.ofReal S⁻¹ * (ENNReal.ofReal S *
          ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2)) ∂ν.totalVariation) := by
        rw [hratio]; exact mul_le_mul le_rfl hint zero_le zero_le
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hS.le), inv_mul_cancel₀ hS.ne',
          ENNReal.ofReal_one, one_mul]


/-- Original R1-HT1 root: exact weighted gap leakage. (1) Measure form (HT1.7): for
every complex mixer with exponential moment a > 1/2 and its genuine mixture ν,
∫_(0,1) x^(-a-1/2) d|ν| ≥ ζ(2a+1)/ζ(a+1/2) ∫_(-∞,0) e^(-a t) d|σ| with the genuine complex
variations |σ|, |ν|; the same exact bound holds for each real Jordan part and for the
coordinate variation control. (2) Continuous-density supremum form (HT1.9) at the endpoint
exponent b for the paper's density r_h, without any b-moment. (3) The measure form applies to
h dt at every a ∈ (1/2, b), while (4) the endpoint b-moment may be infinite under the supremum
hypotheses. (5) r_h is the actual density: for the genuine mixer h(t) dt the four coordinate
mixtures have explicit finite densities D_i on (0,∞) and r_h = (D_0 - D_1) + i (D_2 - D_3). -/
theorem weighted_gap_leakage :
    (∀ (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
        (hm : mixingExponentialMoment a σ < ∞),
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).totalVariation ∧
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.rePart.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).rePart.totalVariation ∧
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.imPart.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).imPart.totalVariation ∧
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.variationControl ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).variationControl) ∧
    (∀ (h : ℝ → ℂ) (H b : ℝ), 1 / 2 < b → Continuous h → (∀ t, h (-t) = h t) →
      (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      ENNReal.ofReal ((riemannZeta ((2 * b + 1 : ℝ) : ℂ) / riemannZeta ((b + 1 / 2 : ℝ) : ℂ)).re) *
          (⨆ t ∈ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (b * t) * ‖h t‖)) ≤
        ⨆ x ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (1 / 2 - b) * ‖mixtureDensity h x‖)) ∧
    (∀ (h : ℝ → ℂ) (H a b : ℝ), a < b → (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      ∫⁻ t, ENNReal.ofReal (Real.exp (a * |t|) * ‖h t‖) < ∞) ∧
    (∀ b : ℝ, 1 / 2 < b → ∃ h : ℝ → ℂ, Continuous h ∧ (∀ t, h (-t) = h t) ∧
      (∀ t, ‖h t‖ ≤ 1 * Real.exp (-b * |t|)) ∧
      ∫⁻ t, ENNReal.ofReal (Real.exp (b * |t|) * ‖h t‖) = ∞) ∧
    (∀ (h : ℝ → ℂ) (hc : Continuous h) (H b : ℝ), 1 / 2 < b →
      (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      (∀ a : ℝ, a < b → mixingExponentialMoment a (densityMixer h hc) < ∞) ∧
      (∀ i : Fin 4, ∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioi 0 →
        positiveDilationMixture (mixingCoordinate (densityMixer h hc) i) s =
          ∫⁻ x in s, positiveMixtureDensity
            (fun t => ENNReal.ofReal (densityCoordinate h i t)) x) ∧
      (∀ i : Fin 4, ∀ x : ℝ, 0 < x →
        positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h i t)) x < ∞) ∧
      (∀ x : ℝ, 0 < x → mixtureDensity h x =
        (((positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 0 t)) x).toReal -
          (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 1 t)) x).toReal :
            ℝ) : ℂ) +
        Complex.I * (((positiveMixtureDensity
            (fun t => ENNReal.ofReal (densityCoordinate h 2 t)) x).toReal -
          (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 3 t)) x).toReal :
            ℝ) : ℂ))) := by
  refine ⟨fun σ a ha hm => ⟨complex_gap_leakage σ a ha hm, ?_⟩,
    fun h H b hb hc he hd => density_gap_leakage_sup hb hc he hd,
    fun h H a b hab hd => lintegral_exp_mul_abs_decay_lt_top hab hd,
    fun b _ => ⟨_, endpoint_density_witness b⟩,
    fun h hc H b hb hd => ⟨fun a hab => densityMixer_moment hc hab hd,
      densityMixer_mixture_density hc hb hd⟩⟩
  have hs : 1 < a + 1 / 2 := by linarith
  set S := ∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) with hSdef
  have hS : 0 < S := tsum_abs_moebius_rpow_pos hs
  have hratio : (riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re = S⁻¹ := by
    rw [← zeta_ratio_re hs]; congr 3; ring_nf
  have hMnorm : weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) = ENNReal.ofReal S :=
    weightedLogNorm_moebiusComb ha
  obtain ⟨-, -, -, -, hinvre, hinvim, -⟩ := weighted_mobius_inverse σ a ha hm
  -- one Jordan pair at a time
  have hpart (P Q : Measure ℝ) (ηp ηn : Measure ℝ) [SFinite ηp] [SFinite ηn]
      (νp νn : Measure ℝ) (hηp : ηp = positiveLogMeasure νp) (hηn : ηn = positiveLogMeasure νn)
      (hPQ : P ⟂ₘ Q)
      (hinv : P + (moebiusPlusComb ∗ ηn + moebiusMinusComb ∗ ηp) =
        Q + (moebiusPlusComb ∗ ηp + moebiusMinusComb ∗ ηn)) :
      ENNReal.ofReal S⁻¹ * ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂(P + Q) ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2)) ∂(νp + νn) := by
    have hL := jordan_gap_leakage a hPQ hinv
    have hη : ∫⁻ y in Iio 0, ENNReal.ofReal (Real.exp (-a * y)) ∂(ηp + ηn) =
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2)) ∂(νp + νn) := by
      rw [Measure.restrict_add, lintegral_add_measure, hηp, hηn,
        setLIntegral_positiveLogMeasure_Iio, setLIntegral_positiveLogMeasure_Iio,
        ← lintegral_add_measure, ← Measure.restrict_add]
    rw [hMnorm, hη] at hL
    calc ENNReal.ofReal S⁻¹ * ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂(P + Q) ≤
        ENNReal.ofReal S⁻¹ * (ENNReal.ofReal S *
          ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2)) ∂(νp + νn)) :=
          mul_le_mul le_rfl hL zero_le zero_le
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hS.le), inv_mul_cancel₀ hS.ne',
            ENNReal.ofReal_one, one_mul]
  have hre := hpart _ _ _ _ _ _ rfl rfl σ.rePart.mutuallySingular hinvre
  have him := hpart _ _ _ _ _ _ rfl rfl σ.imPart.mutuallySingular hinvim
  rw [hratio]
  refine ⟨hre, him, ?_⟩
  change ENNReal.ofReal S⁻¹ * ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t))
      ∂(σ.rePart.totalVariation + σ.imPart.totalVariation) ≤
    ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
      ∂((weightedDilationMixture σ a ha.le hm).rePart.totalVariation +
        (weightedDilationMixture σ a ha.le hm).imPart.totalVariation)
  rw [Measure.restrict_add, lintegral_add_measure, mul_add, Measure.restrict_add,
    lintegral_add_measure]
  exact add_le_add hre him

#print axioms Zeta23.OPICAFollowup.weighted_mixture_exists_fourier
#print axioms Zeta23.OPICAFollowup.weighted_mobius_inverse
#print axioms Zeta23.OPICAFollowup.weighted_mixture_sharp_gap
#print axioms Zeta23.OPICAFollowup.weighted_gap_leakage

end Zeta23.OPICAFollowup
