
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Zeta23.OPICA.LocallyFiniteSignedMeasure
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.Tactic

/-! Actual locally finite complex measures are pairs of real locally finite
Jordan measures. No finiteness on the whole line is required. Finite complex
measures are used only after restriction to a compact set. -/

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology SchwartzMap
namespace Zeta23.OPICAFollowup

structure LocallyFiniteComplexMeasure where
  rePart : Zeta23.OPICA.LocallyFiniteSignedMeasure
  imPart : Zeta23.OPICA.LocallyFiniteSignedMeasure

@[ext] theorem LocallyFiniteComplexMeasure.ext {mu nu : LocallyFiniteComplexMeasure}
    (hreal : mu.rePart=nu.rePart) (himag : mu.imPart=nu.imPart) : mu=nu := by
  cases mu
  cases nu
  cases hreal
  cases himag
  rfl

/-- Positive coordinate variation controls the actual complex total variation.
It is not relabelled as the Euclidean complex total variation. -/
def LocallyFiniteComplexMeasure.variationControl (mu : LocallyFiniteComplexMeasure) : Measure ℝ :=
  mu.rePart.totalVariation+mu.imPart.totalVariation

instance LocallyFiniteComplexMeasure.variationControl_locallyFinite (mu : LocallyFiniteComplexMeasure) :
    IsLocallyFiniteMeasure mu.variationControl where
  finiteAtNhds x := by
    obtain ⟨s,hs,hsfinite⟩ := mu.rePart.totalVariation.finiteAt_nhds x
    obtain ⟨t,ht,htfinite⟩ := mu.imPart.totalVariation.finiteAt_nhds x
    refine ⟨s∩t,Filter.inter_mem hs ht,?_⟩
    rw [variationControl,Measure.add_apply]
    exact ENNReal.add_lt_top.mpr
      ⟨(measure_mono inter_subset_left).trans_lt hsfinite,
        (measure_mono inter_subset_right).trans_lt htfinite⟩

def LocallyFiniteComplexMeasure.HasLinearGrowth (mu : LocallyFiniteComplexMeasure) : Prop :=
  Zeta23.OPICA.LinearMassGrowth mu.variationControl

theorem LocallyFiniteComplexMeasure.re_hasLinearGrowth (mu : LocallyFiniteComplexMeasure)
    (hmu : mu.HasLinearGrowth) : mu.rePart.HasLinearGrowth := by
  apply hmu.mono
  intro s
  rw [variationControl,Measure.add_apply]
  exact le_add_of_nonneg_right zero_le

theorem LocallyFiniteComplexMeasure.im_hasLinearGrowth (mu : LocallyFiniteComplexMeasure)
    (hmu : mu.HasLinearGrowth) : mu.imPart.HasLinearGrowth := by
  apply hmu.mono
  intro s
  rw [variationControl,Measure.add_apply]
  exact le_add_of_nonneg_left zero_le

/-- The true signed restriction to a compact set, obtained from its two finite
positive Jordan restrictions, without subtracting infinite global masses. -/
def localSignedCompactRestriction (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) : SignedMeasure ℝ :=
  letI : IsFiniteMeasure (mu.positive.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  letI : IsFiniteMeasure (mu.negative.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  (mu.positive.restrict K).toSignedMeasure-(mu.negative.restrict K).toSignedMeasure

def LocallyFiniteComplexMeasure.compactRestriction (mu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) : ComplexMeasure ℝ :=
  (localSignedCompactRestriction mu.rePart K hK).toComplexMeasure
    (localSignedCompactRestriction mu.imPart K hK)

theorem LocallyFiniteComplexMeasure.compactRestriction_re (mu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (mu.compactRestriction K hK).re=localSignedCompactRestriction mu.rePart K hK := rfl

theorem LocallyFiniteComplexMeasure.compactRestriction_im (mu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (mu.compactRestriction K hK).im=localSignedCompactRestriction mu.imPart K hK := rfl

/-- Local convergence uses the genuine finite complex variation of the
restriction difference, not merely convergence against a chosen test family. -/
def LocalVariationConvergence (seq : ℕ → LocallyFiniteComplexMeasure)
    (mu : LocallyFiniteComplexMeasure) : Prop :=
  ∀ K : Set ℝ, ∀ hK : IsCompact K, Tendsto
    (fun n => ((seq n).compactRestriction K hK-mu.compactRestriction K hK).variation.real univ)
      atTop (𝓝 0)

def LocallyFiniteComplexMeasure.integral (mu : LocallyFiniteComplexMeasure) (f : ℝ → ℂ) : ℂ :=
  ((∫ x, f x ∂mu.rePart.positive)-(∫ x, f x ∂mu.rePart.negative))+
    I*((∫ x, f x ∂mu.imPart.positive)-(∫ x, f x ∂mu.imPart.negative))

def LocallyFiniteComplexMeasure.distributionOfLinearGrowth (mu : LocallyFiniteComplexMeasure)
    (hmu : mu.HasLinearGrowth) : TemperedDistribution ℝ ℂ :=
  mu.rePart.distributionOfLinearGrowth (mu.re_hasLinearGrowth hmu)+
    I • mu.imPart.distributionOfLinearGrowth (mu.im_hasLinearGrowth hmu)

theorem LocallyFiniteComplexMeasure.distributionOfLinearGrowth_apply
    (mu : LocallyFiniteComplexMeasure) (hmu : mu.HasLinearGrowth) (f : SchwartzMap ℝ ℂ) :
    mu.distributionOfLinearGrowth hmu f=mu.integral f := rfl

def complexSchwartzConj (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem realJordan_distribution_conj (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (hmu : mu.HasLinearGrowth) (f : SchwartzMap ℝ ℂ) :
    mu.distributionOfLinearGrowth hmu (complexSchwartzConj f)=
      starRingEnd ℂ (mu.distributionOfLinearGrowth hmu f) := by
  rw [mu.distributionOfLinearGrowth_apply,mu.distributionOfLinearGrowth_apply]
  change (∫ x, starRingEnd ℂ (f x) ∂mu.positive)-
    (∫ x, starRingEnd ℂ (f x) ∂mu.negative)=_
  rw [integral_conj,integral_conj,map_sub]

theorem LocallyFiniteComplexMeasure.real_imag_distributions_of_eq
    (mu nu : LocallyFiniteComplexMeasure) (hmu : mu.HasLinearGrowth) (hnu : nu.HasLinearGrowth)
    (heq : mu.distributionOfLinearGrowth hmu=nu.distributionOfLinearGrowth hnu) :
    mu.rePart.distributionOfLinearGrowth (mu.re_hasLinearGrowth hmu)=
      nu.rePart.distributionOfLinearGrowth (nu.re_hasLinearGrowth hnu) ∧
    mu.imPart.distributionOfLinearGrowth (mu.im_hasLinearGrowth hmu)=
      nu.imPart.distributionOfLinearGrowth (nu.im_hasLinearGrowth hnu) := by
  have hpoint (f : SchwartzMap ℝ ℂ) := congrArg (fun T : TemperedDistribution ℝ ℂ => T f) heq
  have hconj (f : SchwartzMap ℝ ℂ) := hpoint (complexSchwartzConj f)
  have hpair (f : SchwartzMap ℝ ℂ) :
      mu.rePart.distributionOfLinearGrowth (mu.re_hasLinearGrowth hmu) f-
        I*mu.imPart.distributionOfLinearGrowth (mu.im_hasLinearGrowth hmu) f=
      nu.rePart.distributionOfLinearGrowth (nu.re_hasLinearGrowth hnu) f-
        I*nu.imPart.distributionOfLinearGrowth (nu.im_hasLinearGrowth hnu) f := by
    have h := hconj f
    change mu.rePart.distributionOfLinearGrowth (mu.re_hasLinearGrowth hmu) (complexSchwartzConj f)+
      I*mu.imPart.distributionOfLinearGrowth (mu.im_hasLinearGrowth hmu) (complexSchwartzConj f)=
      nu.rePart.distributionOfLinearGrowth (nu.re_hasLinearGrowth hnu) (complexSchwartzConj f)+
        I*nu.imPart.distributionOfLinearGrowth (nu.im_hasLinearGrowth hnu) (complexSchwartzConj f) at h
    rw [realJordan_distribution_conj,realJordan_distribution_conj,
      realJordan_distribution_conj,realJordan_distribution_conj] at h
    have hh := congrArg (starRingEnd ℂ) h
    simpa only [map_add,map_mul,Complex.conj_conj,Complex.conj_I,neg_mul,sub_eq_add_neg] using hh
  constructor
  · ext f
    have h := hpoint f
    change mu.rePart.distributionOfLinearGrowth (mu.re_hasLinearGrowth hmu) f+
      I*mu.imPart.distributionOfLinearGrowth (mu.im_hasLinearGrowth hmu) f=
      nu.rePart.distributionOfLinearGrowth (nu.re_hasLinearGrowth hnu) f+
        I*nu.imPart.distributionOfLinearGrowth (nu.im_hasLinearGrowth hnu) f at h
    linear_combination (1/2:ℂ)*h+(1/2:ℂ)*hpair f
  · ext f
    apply mul_left_cancel₀ Complex.I_ne_zero
    have h := hpoint f
    change mu.rePart.distributionOfLinearGrowth (mu.re_hasLinearGrowth hmu) f+
      I*mu.imPart.distributionOfLinearGrowth (mu.im_hasLinearGrowth hmu) f=
      nu.rePart.distributionOfLinearGrowth (nu.re_hasLinearGrowth hnu) f+
        I*nu.imPart.distributionOfLinearGrowth (nu.im_hasLinearGrowth hnu) f at h
    linear_combination (1/2:ℂ)*h-(1/2:ℂ)*hpair f

theorem LocallyFiniteComplexMeasure.distributionOfLinearGrowth_injective :
    Function.Injective (fun mu : {mu : LocallyFiniteComplexMeasure // mu.HasLinearGrowth} =>
      mu.val.distributionOfLinearGrowth mu.property) := by
  intro mu nu heq
  apply Subtype.ext
  obtain ⟨hre,him⟩ := mu.val.real_imag_distributions_of_eq nu.val mu.property nu.property heq
  apply LocallyFiniteComplexMeasure.ext
  · have h := Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_injective
      (a₁ := ⟨mu.val.rePart,mu.val.re_hasLinearGrowth mu.property⟩)
      (a₂ := ⟨nu.val.rePart,nu.val.re_hasLinearGrowth nu.property⟩) hre
    exact congrArg Subtype.val h
  · have h := Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_injective
      (a₁ := ⟨mu.val.imPart,mu.val.im_hasLinearGrowth mu.property⟩)
      (a₂ := ⟨nu.val.imPart,nu.val.im_hasLinearGrowth nu.property⟩) him
    exact congrArg Subtype.val h



def localMeasureInterval (n : ℕ) : Set ℝ := Icc (-(n:ℝ)) (n:ℝ)

theorem localMeasureInterval_cover : (⋃ n : ℕ, localMeasureInterval n)=univ := by
  ext x
  simp only [mem_iUnion,mem_univ,iff_true]
  obtain ⟨n,hn⟩ := exists_nat_gt |x|
  exact ⟨n,abs_le.mp hn.le⟩

instance locallyFiniteMeasure_sub (mu nu : Measure ℝ) [IsLocallyFiniteMeasure mu] :
    IsLocallyFiniteMeasure (mu-nu) where
  finiteAtNhds x := by
    obtain ⟨s,hs,hfinite⟩ := mu.finiteAt_nhds x
    exact ⟨s,hs,(Measure.sub_le s).trans_lt hfinite⟩

/-- Global mutual singularity follows from finite Jordan decomposition on an
exhaustion. Neither original positive measure is required globally finite. -/
theorem locallyFiniteMeasure_sub_mutuallySingular (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu] :
    (mu-nu).MutuallySingular (nu-mu) := by
  apply Measure.mutuallySingular_of_disjoint
  rw [disjoint_iff]
  apply Measure.ext_of_iUnion_eq_univ localMeasureInterval_cover
  intro n
  let K := localMeasureInterval n
  have hK : IsCompact K := isCompact_Icc
  let : IsFiniteMeasure (mu.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (nu.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hleft : ((mu-nu)⊓(nu-mu)).restrict K≤mu.restrict K-nu.restrict K := by
    rw [←Measure.restrict_sub_eq_restrict_sub_restrict hK.measurableSet]
    exact Measure.restrict_mono subset_rfl inf_le_left
  have hright : ((mu-nu)⊓(nu-mu)).restrict K≤nu.restrict K-mu.restrict K := by
    rw [←Measure.restrict_sub_eq_restrict_sub_restrict hK.measurableSet]
    exact Measure.restrict_mono subset_rfl inf_le_right
  have hd := (Measure.mutually_singular_measure_sub
    (μ := mu.restrict K) (ν := nu.restrict K)).disjoint
  have hbot : ((mu.restrict K-nu.restrict K)⊓(nu.restrict K-mu.restrict K))=0 :=
    disjoint_iff.mp hd
  change ((mu-nu)⊓(nu-mu)).restrict K=(0:Measure ℝ).restrict K
  rw [Measure.restrict_zero]
  exact le_antisymm ((le_inf hleft hright).trans (le_of_eq hbot)) (Measure.zero_le _)

theorem finiteMeasure_jordan_cross_sum (mu nu : Measure ℝ)
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    (mu-nu)+nu=(nu-mu)+mu := by
  apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
  rw [Measure.toSignedMeasure_add,Measure.toSignedMeasure_add]
  have h := Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub (μ := mu) (ν := nu)
  have hcross := sub_eq_sub_iff_add_eq_add.mp h.symm
  simpa only [add_comm] using hcross

theorem locallyFiniteMeasure_jordan_cross_sum (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu] :
    (mu-nu)+nu=(nu-mu)+mu := by
  apply Measure.ext_of_iUnion_eq_univ localMeasureInterval_cover
  intro n
  have hK : IsCompact (localMeasureInterval n) := isCompact_Icc
  let : IsFiniteMeasure (mu.restrict (localMeasureInterval n)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (nu.restrict (localMeasureInterval n)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  rw [Measure.restrict_add,Measure.restrict_add,
    Measure.restrict_sub_eq_restrict_sub_restrict hK.measurableSet,
    Measure.restrict_sub_eq_restrict_sub_restrict hK.measurableSet]
  exact finiteMeasure_jordan_cross_sum _ _

def localJordanDifference (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu] :
    Zeta23.OPICA.LocallyFiniteSignedMeasure where
  positive := mu-nu
  negative := nu-mu
  positive_locallyFinite := inferInstance
  negative_locallyFinite := inferInstance
  mutuallySingular := locallyFiniteMeasure_sub_mutuallySingular mu nu

theorem localJordanDifference_variation_le (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu] :
    (localJordanDifference mu nu).totalVariation≤mu+nu := by
  exact add_le_add Measure.sub_le Measure.sub_le

theorem localJordanDifference_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu nu : Measure ℝ) [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu]
    (f : ℝ → E) (hmu : Integrable f mu) (hnu : Integrable f nu) :
    ((∫ x, f x ∂(localJordanDifference mu nu).positive)-
      (∫ x, f x ∂(localJordanDifference mu nu).negative))=
        (∫ x, f x ∂mu)-(∫ x, f x ∂nu) := by
  have hpos : Integrable f (mu-nu) := hmu.mono_measure Measure.sub_le
  have hneg : Integrable f (nu-mu) := hnu.mono_measure Measure.sub_le
  have heq := congrArg (fun eta : Measure ℝ => ∫ x, f x ∂eta)
    (locallyFiniteMeasure_jordan_cross_sum mu nu)
  rw [integral_add_measure hpos hnu,integral_add_measure hneg hmu] at heq
  change (∫ x, f x ∂(mu-nu))-(∫ x, f x ∂(nu-mu))=_
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using heq)


theorem localSignedCompactRestriction_apply (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ) (hE : MeasurableSet E) :
    localSignedCompactRestriction mu K hK E=
      (mu.positive.restrict K).real E-(mu.negative.restrict K).real E := by
  let : IsFiniteMeasure (mu.positive.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (mu.negative.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  simp only [localSignedCompactRestriction,_root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable hE]

theorem localSignedCompactRestriction_norm_le (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ) (hE : MeasurableSet E) :
    |localSignedCompactRestriction mu K hK E|≤(mu.totalVariation.restrict K).real E := by
  let : IsFiniteMeasure (mu.positive.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (mu.negative.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  rw [localSignedCompactRestriction_apply mu K hK E hE]
  calc
    _ ≤ |(mu.positive.restrict K).real E|+|(mu.negative.restrict K).real E| := abs_sub _ _
    _ = (mu.positive.restrict K).real E+(mu.negative.restrict K).real E := by
      rw [abs_of_nonneg measureReal_nonneg,abs_of_nonneg measureReal_nonneg]
    _ = _ := by
      rw [Zeta23.OPICA.LocallyFiniteSignedMeasure.totalVariation,Measure.restrict_add,
        measureReal_add_apply]

theorem LocallyFiniteComplexMeasure.compactRestriction_norm_le (mu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ) (hE : MeasurableSet E) :
    ‖mu.compactRestriction K hK E‖≤(mu.variationControl.restrict K).real E := by
  let : IsFiniteMeasure (mu.rePart.totalVariation.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (mu.imPart.totalVariation.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  calc
    _ ≤ |(mu.compactRestriction K hK E).re|+|(mu.compactRestriction K hK E).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |localSignedCompactRestriction mu.rePart K hK E|+
      |localSignedCompactRestriction mu.imPart K hK E| := rfl
    _ ≤ (mu.rePart.totalVariation.restrict K).real E+(mu.imPart.totalVariation.restrict K).real E :=
      add_le_add (localSignedCompactRestriction_norm_le mu.rePart K hK E hE)
        (localSignedCompactRestriction_norm_le mu.imPart K hK E hE)
    _ = _ := by rw [variationControl,Measure.restrict_add,measureReal_add_apply]

theorem LocallyFiniteComplexMeasure.compactRestriction_variation_le (mu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (mu.compactRestriction K hK).variation≤mu.variationControl.restrict K := by
  let : IsFiniteMeasure (mu.variationControl.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  rw [←ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal (mu.compactRestriction_norm_le K hK E hE)).trans_eq
    (ENNReal.ofReal_toReal (measure_ne_top _ _))

instance LocallyFiniteComplexMeasure.compactRestriction_variation_finite (mu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) : IsFiniteMeasure (mu.compactRestriction K hK).variation := by
  let : IsFiniteMeasure (mu.variationControl.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact isFiniteMeasure_of_le _ (mu.compactRestriction_variation_le K hK)

/-- Canonical complex variation is the supremum of the actual Euclidean
complex variations on a compact exhaustion. -/
def LocallyFiniteComplexMeasure.totalVariation (mu : LocallyFiniteComplexMeasure) : Measure ℝ :=
  ⨆ n : ℕ, (mu.compactRestriction (localMeasureInterval n) isCompact_Icc).variation

theorem LocallyFiniteComplexMeasure.totalVariation_le_control (mu : LocallyFiniteComplexMeasure) :
    mu.totalVariation≤mu.variationControl := by
  apply iSup_le
  intro n
  exact (mu.compactRestriction_variation_le _ isCompact_Icc).trans Measure.restrict_le_self

instance LocallyFiniteComplexMeasure.totalVariation_locallyFinite (mu : LocallyFiniteComplexMeasure) :
    IsLocallyFiniteMeasure mu.totalVariation where
  finiteAtNhds x := by
    obtain ⟨s,hs,hfinite⟩ := mu.variationControl.finiteAt_nhds x
    exact ⟨s,hs,(mu.totalVariation_le_control s).trans_lt hfinite⟩

theorem complexMeasure_re_variation_le (c : ComplexMeasure ℝ) : c.re.variation≤c.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  calc
    ‖c.re E‖ₑ = ENNReal.ofReal |(c E).re| := by rw [←ofReal_norm]; rfl
    _ ≤ ENNReal.ofReal ‖c E‖ := ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
    _ = ‖c E‖ₑ := ofReal_norm _
    _ ≤ c.variation E := VectorMeasure.enorm_measure_le_variation _ _

theorem complexMeasure_im_variation_le (c : ComplexMeasure ℝ) : c.im.variation≤c.variation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  calc
    ‖c.im E‖ₑ = ENNReal.ofReal |(c E).im| := by rw [←ofReal_norm]; rfl
    _ ≤ ENNReal.ofReal ‖c E‖ := ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)
    _ = ‖c E‖ₑ := ofReal_norm _
    _ ≤ c.variation E := VectorMeasure.enorm_measure_le_variation _ _

instance complexMeasure_re_variation_finite (c : ComplexMeasure ℝ)
    [IsFiniteMeasure c.variation] : IsFiniteMeasure c.re.variation :=
  isFiniteMeasure_of_le _ (complexMeasure_re_variation_le c)

instance complexMeasure_im_variation_finite (c : ComplexMeasure ℝ)
    [IsFiniteMeasure c.variation] : IsFiniteMeasure c.im.variation :=
  isFiniteMeasure_of_le _ (complexMeasure_im_variation_le c)

instance complexMeasure_sub_variation_finite (c d : ComplexMeasure ℝ)
    [IsFiniteMeasure c.variation] [IsFiniteMeasure d.variation] :
    IsFiniteMeasure (c-d).variation :=
  isFiniteMeasure_of_le _ VectorMeasure.variation_sub_le

/-- Integration of a complex test against a finite complex measure, with its
two genuine real vector-measure integrals. -/
def finiteComplexIntegral (c : ComplexMeasure ℝ) (f : ℝ→ℂ) : ℂ :=
  (∫ᵛ x, f x ∂<•c.re)+I*(∫ᵛ x, f x ∂<•c.im)

theorem finiteComplexIntegral_norm_le (c : ComplexMeasure ℝ)
    [IsFiniteMeasure c.variation] (f : ℝ→ℂ) (C : ℝ)
    (hC : 0≤C) (hf : ∀x,‖f x‖≤C) :
    ‖finiteComplexIntegral c f‖≤2*C*c.variation.real univ := by
  have hre : ‖∫ᵛ x, f x ∂<•c.re‖≤C*c.re.variation.real univ := by
    simpa using (VectorMeasure.norm_integral_le_of_norm_le_const
      (μ := c.re) (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (Filter.Eventually.of_forall hf))
  have him : ‖∫ᵛ x, f x ∂<•c.im‖≤C*c.im.variation.real univ := by
    simpa using (VectorMeasure.norm_integral_le_of_norm_le_const
      (μ := c.im) (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      (Filter.Eventually.of_forall hf))
  have hreal := ENNReal.toReal_mono (measure_ne_top c.variation univ)
    (complexMeasure_re_variation_le c univ)
  have himag := ENNReal.toReal_mono (measure_ne_top c.variation univ)
    (complexMeasure_im_variation_le c univ)
  calc
    _ ≤ ‖∫ᵛ x, f x ∂<•c.re‖+‖I*(∫ᵛ x, f x ∂<•c.im)‖ := norm_add_le _ _
    _ = ‖∫ᵛ x, f x ∂<•c.re‖+‖∫ᵛ x, f x ∂<•c.im‖ := by simp only [norm_mul, norm_I,one_mul]
    _ ≤ C*c.re.variation.real univ+C*c.im.variation.real univ := add_le_add hre him
    _ ≤ 2*C*c.variation.real univ := by
      change (c.re.variation univ).toReal≤(c.variation univ).toReal at hreal
      change (c.im.variation univ).toReal≤(c.variation univ).toReal at himag
      dsimp only [Measure.real]
      nlinarith

theorem finiteComplexIntegral_sub (c d : ComplexMeasure ℝ)
    [IsFiniteMeasure c.variation] [IsFiniteMeasure d.variation]
    (f : ℝ→ℂ) (hf : StronglyMeasurable f) (C : ℝ) (hbound : ∀x,‖f x‖≤C) :
    finiteComplexIntegral (c-d) f=finiteComplexIntegral c f-finiteComplexIntegral d f := by
  have hcr : c.re.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbound)
  have hci : c.im.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbound)
  have hdr : d.re.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbound)
  have hdi : d.im.Integrable f := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbound)
  simp only [finiteComplexIntegral,map_sub,VectorMeasure.integral_sub_vectorMeasure hcr hdr,
    VectorMeasure.integral_sub_vectorMeasure hci hdi]
  ring

theorem LocalVariationConvergence.tendsto_local_test
    {seq : ℕ→LocallyFiniteComplexMeasure} {mu : LocallyFiniteComplexMeasure}
    (h : LocalVariationConvergence seq mu) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ→ℂ) (hf : StronglyMeasurable f) (C : ℝ) (hC : 0≤C) (hbound : ∀x,‖f x‖≤C) :
    Tendsto (fun n => finiteComplexIntegral ((seq n).compactRestriction K hK) f)
      atTop (𝓝 (finiteComplexIntegral (mu.compactRestriction K hK) f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _
    (by simpa using (h K hK).const_mul (2*C))
  intro n
  rw [←finiteComplexIntegral_sub _ _ f hf C hbound]
  exact finiteComplexIntegral_norm_le _ f C hC hbound

open scoped NNReal ENNReal

instance locallyFiniteMeasure_add (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu] : IsLocallyFiniteMeasure (mu+nu) where
  finiteAtNhds x := by
    obtain ⟨s,hs,hfinite⟩ := mu.finiteAt_nhds x
    obtain ⟨t,ht,htfinite⟩ := nu.finiteAt_nhds x
    refine ⟨s∩t,Filter.inter_mem hs ht,?_⟩
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨(measure_mono inter_subset_left).trans_lt hfinite,
      (measure_mono inter_subset_right).trans_lt htfinite⟩

instance locallyFiniteMeasure_smul_nnreal (a : ℝ≥0) (mu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] : IsLocallyFiniteMeasure (a • mu) where
  finiteAtNhds x := by
    obtain ⟨s,hs,hfinite⟩ := mu.finiteAt_nhds x
    refine ⟨s,hs,?_⟩
    change (a:ℝ≥0∞)*mu s<∞
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite

def localSignedCompactJordan (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) : JordanDecomposition ℝ where
  posPart := mu.positive.restrict K
  negPart := mu.negative.restrict K
  posPart_finite := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  negPart_finite := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  mutuallySingular := ((mu.mutuallySingular.restrict K).symm.restrict K).symm

theorem localSignedCompactRestriction_jordan (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (localSignedCompactRestriction mu K hK).toJordanDecomposition=localSignedCompactJordan mu K hK := by
  change (localSignedCompactJordan mu K hK).toSignedMeasure.toJordanDecomposition=_
  exact JordanDecomposition.toJordanDecomposition_toSignedMeasure (localSignedCompactJordan mu K hK)

theorem localSignedCompactRestriction_variation (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (localSignedCompactRestriction mu K hK).variation=mu.totalVariation.restrict K := by
  rw [←SignedMeasure.totalVariation_eq_variation,SignedMeasure.totalVariation,
    localSignedCompactRestriction_jordan]
  exact (Measure.restrict_add _ _ _).symm

theorem localJordanDifference_compactRestriction (mu nu : Measure ℝ)
    [IsLocallyFiniteMeasure mu] [IsLocallyFiniteMeasure nu]
    (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction (localJordanDifference mu nu) K hK=
      (let : IsFiniteMeasure (mu.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
       let : IsFiniteMeasure (nu.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
       (mu.restrict K).toSignedMeasure-(nu.restrict K).toSignedMeasure) := by
  let : IsFiniteMeasure (mu.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (nu.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  dsimp only [localSignedCompactRestriction,localJordanDifference]
  simp only [Measure.restrict_sub_eq_restrict_sub_restrict hK.measurableSet]
  exact (Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub).symm

def localJordanAdd (mu nu : Zeta23.OPICA.LocallyFiniteSignedMeasure) :
    Zeta23.OPICA.LocallyFiniteSignedMeasure :=
  localJordanDifference (mu.positive+nu.positive) (mu.negative+nu.negative)

def localJordanScale (a : ℝ) (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure) :
    Zeta23.OPICA.LocallyFiniteSignedMeasure :=
  localJordanDifference
    (Real.toNNReal a • mu.positive+Real.toNNReal (-a) • mu.negative)
    (Real.toNNReal a • mu.negative+Real.toNNReal (-a) • mu.positive)

theorem localJordanAdd_compactRestriction (mu nu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction (localJordanAdd mu nu) K hK=
      localSignedCompactRestriction mu K hK+localSignedCompactRestriction nu K hK := by
  let : IsFiniteMeasure (mu.positive.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (mu.negative.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (nu.positive.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (nu.negative.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  rw [localJordanAdd,localJordanDifference_compactRestriction]
  simp only [Measure.restrict_add,Measure.toSignedMeasure_add,localSignedCompactRestriction]
  abel

theorem localJordanScale_compactRestriction (a : ℝ) (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction (localJordanScale a mu) K hK=
      a • localSignedCompactRestriction mu K hK := by
  let : IsFiniteMeasure (mu.positive.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (mu.negative.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  rw [localJordanScale,localJordanDifference_compactRestriction]
  simp only [Measure.restrict_add,Measure.restrict_smul,Measure.toSignedMeasure_add,
    Measure.toSignedMeasure_smul,localSignedCompactRestriction]
  simp only [NNReal.smul_def,smul_sub]
  have ha : (Real.toNNReal a:ℝ)-(Real.toNNReal (-a):ℝ)=a := by
    rw [Real.coe_toNNReal',Real.coe_toNNReal']
    rcases le_total 0 a with ha|ha
    · simp [max_eq_left ha,max_eq_right (neg_nonpos.mpr ha)]
    · simp [max_eq_right ha,max_eq_left (neg_nonneg.mpr ha)]
  conv_rhs => rw [←ha]
  simp only [sub_smul]
  abel

def LocallyFiniteComplexMeasure.add (mu nu : LocallyFiniteComplexMeasure) : LocallyFiniteComplexMeasure :=
  ⟨localJordanAdd mu.rePart nu.rePart,localJordanAdd mu.imPart nu.imPart⟩

def LocallyFiniteComplexMeasure.scale (c : ℂ) (mu : LocallyFiniteComplexMeasure) : LocallyFiniteComplexMeasure :=
  ⟨localJordanAdd (localJordanScale c.re mu.rePart) (localJordanScale (-c.im) mu.imPart),
    localJordanAdd (localJordanScale c.im mu.rePart) (localJordanScale c.re mu.imPart)⟩

theorem LocallyFiniteComplexMeasure.compactRestriction_add (mu nu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (mu.add nu).compactRestriction K hK=mu.compactRestriction K hK+nu.compactRestriction K hK := by
  ext E hE
  apply Complex.ext <;>
    simp only [compactRestriction,add,SignedMeasure.toComplexMeasure_apply,
      localJordanAdd_compactRestriction,Complex.add_re,Complex.add_im,_root_.add_apply]

theorem LocallyFiniteComplexMeasure.compactRestriction_scale (c : ℂ) (mu : LocallyFiniteComplexMeasure)
    (K : Set ℝ) (hK : IsCompact K) :
    (mu.scale c).compactRestriction K hK=c • mu.compactRestriction K hK := by
  ext E hE
  apply Complex.ext <;>
    simp [compactRestriction,scale,SignedMeasure.toComplexMeasure_apply,
      localJordanAdd_compactRestriction,localJordanScale_compactRestriction,
      Complex.mul_re,Complex.mul_im,smul_eq_mul] <;> ring


theorem localSignedCompactRestriction_restrict
    (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure) (K L : Set ℝ)
    (hK : IsCompact K) (hL : IsCompact L) :
    (localSignedCompactRestriction mu K hK).restrict L=
      localSignedCompactRestriction mu (K∩L) (hK.inter_right hL.isClosed) := by
  ext E hE
  rw [VectorMeasure.restrict_apply _ hL.measurableSet hE,
    localSignedCompactRestriction_apply _ _ _ _ (hE.inter hL.measurableSet),
    localSignedCompactRestriction_apply _ _ _ _ hE]
  simp only [Measure.real,Measure.restrict_apply (hE.inter hL.measurableSet),
    Measure.restrict_apply hE]
  congr 2 <;> congr 1 <;> ext x <;> simp only [mem_inter_iff] <;> tauto

theorem LocallyFiniteComplexMeasure.compactRestriction_restrict (mu : LocallyFiniteComplexMeasure)
    (K L : Set ℝ) (hK : IsCompact K) (hL : IsCompact L) :
    (mu.compactRestriction K hK).restrict L=
      mu.compactRestriction (K∩L) (hK.inter_right hL.isClosed) := by
  ext E hE
  rw [VectorMeasure.restrict_apply _ hL.measurableSet hE]
  apply Complex.ext
  · change localSignedCompactRestriction mu.rePart K hK (E∩L)=_
    rw [←VectorMeasure.restrict_apply _ hL.measurableSet hE,
      localSignedCompactRestriction_restrict mu.rePart K L hK hL]
    rfl
  · change localSignedCompactRestriction mu.imPart K hK (E∩L)=_
    rw [←VectorMeasure.restrict_apply _ hL.measurableSet hE,
      localSignedCompactRestriction_restrict mu.imPart K L hK hL]
    rfl

theorem LocallyFiniteComplexMeasure.compactRestriction_variation_restrict
    (mu : LocallyFiniteComplexMeasure) (K L : Set ℝ) (hK : IsCompact K) (hL : IsCompact L) :
    (mu.compactRestriction K hK).variation.restrict L=
      (mu.compactRestriction (K∩L) (hK.inter_right hL.isClosed)).variation := by
  rw [←VectorMeasure.variation_restrict hL.measurableSet,mu.compactRestriction_restrict K L hK hL]

theorem LocallyFiniteComplexMeasure.compactRestriction_variation_mono
    (mu : LocallyFiniteComplexMeasure) (K L : Set ℝ) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K⊆L) :
    (mu.compactRestriction K hK).variation≤(mu.compactRestriction L hL).variation := by
  have hset : L∩K=K := inter_eq_right.mpr hKL
  have hr := mu.compactRestriction_variation_restrict L K hL hK
  simp only [hset] at hr
  rw [←hr]
  exact Measure.restrict_le_self

theorem LocallyFiniteComplexMeasure.compactRestriction_variation_self
    (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    (mu.compactRestriction K hK).variation.restrict K=(mu.compactRestriction K hK).variation := by
  simpa only [inter_self] using mu.compactRestriction_variation_restrict K K hK hK

theorem compact_subset_localMeasureInterval (K : Set ℝ) (hK : IsCompact K) :
    ∃ n : ℕ,K⊆localMeasureInterval n := by
  obtain ⟨r,hr⟩ := hK.isBounded.subset_closedBall (0:ℝ)
  obtain ⟨n,hn⟩ := exists_nat_gt r
  refine ⟨n,fun x hx => ?_⟩
  have hdist : |x|≤r := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hr hx
  exact abs_le.mp (hdist.trans hn.le)

theorem LocallyFiniteComplexMeasure.compactRestriction_variation_le_totalVariation
    (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    (mu.compactRestriction K hK).variation≤mu.totalVariation := by
  obtain ⟨n,hn⟩ := compact_subset_localMeasureInterval K hK
  exact (mu.compactRestriction_variation_mono K (localMeasureInterval n) hK isCompact_Icc hn).trans
    (le_iSup (fun n : ℕ => (mu.compactRestriction (localMeasureInterval n) isCompact_Icc).variation) n)

theorem LocallyFiniteComplexMeasure.totalVariation_restrict_compact
    (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    mu.totalVariation.restrict K=(mu.compactRestriction K hK).variation := by
  apply le_antisymm
  · have hbound : mu.totalVariation≤
        (mu.compactRestriction K hK).variation+mu.variationControl.restrict Kᶜ := by
      apply iSup_le
      intro n
      let v := (mu.compactRestriction (localMeasureInterval n) isCompact_Icc).variation
      calc
        v = v.restrict K+v.restrict Kᶜ := (Measure.restrict_add_restrict_compl hK.measurableSet).symm
        _ ≤ (mu.compactRestriction K hK).variation+mu.variationControl.restrict Kᶜ := by
          apply add_le_add
          · rw [show v.restrict K=(mu.compactRestriction ((localMeasureInterval n)∩K)
                (isCompact_Icc.inter_right hK.isClosed)).variation from
                  mu.compactRestriction_variation_restrict _ _ isCompact_Icc hK]
            exact mu.compactRestriction_variation_mono _ K _ hK inter_subset_right
          · exact Measure.restrict_mono subset_rfl
              ((mu.compactRestriction_variation_le _ isCompact_Icc).trans Measure.restrict_le_self)
    have hrestrict := Measure.restrict_mono (s := K) subset_rfl hbound
    simpa only [Measure.restrict_add,mu.compactRestriction_variation_self K hK,
      Measure.restrict_restrict hK.measurableSet,inter_compl_self,Measure.restrict_empty,add_zero]
      using hrestrict
  · rw [←mu.compactRestriction_variation_self K hK]
    exact Measure.restrict_mono subset_rfl (mu.compactRestriction_variation_le_totalVariation K hK)


theorem localSignedCompactRestriction_integral
    (mu : Zeta23.OPICA.LocallyFiniteSignedMeasure) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ→ℂ) (hf : Integrable f (mu.totalVariation.restrict K)) :
    (∫ᵛ x, f x ∂<•localSignedCompactRestriction mu K hK)=
      (∫ x in K,f x ∂mu.positive)-(∫ x in K,f x ∂mu.negative) := by
  let : IsFiniteMeasure (mu.positive.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (mu.negative.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hparts : Integrable f (mu.positive.restrict K) ∧ Integrable f (mu.negative.restrict K) := by
    apply integrable_add_measure.mp
    simpa only [Zeta23.OPICA.LocallyFiniteSignedMeasure.totalVariation,Measure.restrict_add] using hf
  have hp : (mu.positive.restrict K).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hparts.1
  have hn : (mu.negative.restrict K).toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hparts.2
  rw [localSignedCompactRestriction,VectorMeasure.integral_sub_vectorMeasure hp hn,
    VectorMeasure.integral_toSignedMeasure,VectorMeasure.integral_toSignedMeasure]

theorem LocallyFiniteComplexMeasure.finiteComplexIntegral_compactRestriction
    (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ→ℂ) (hf : Integrable f (mu.variationControl.restrict K)) :
    finiteComplexIntegral (mu.compactRestriction K hK) f=
      ((∫ x in K,f x ∂mu.rePart.positive)-(∫ x in K,f x ∂mu.rePart.negative))+
      I*((∫ x in K,f x ∂mu.imPart.positive)-(∫ x in K,f x ∂mu.imPart.negative)) := by
  have hparts : Integrable f (mu.rePart.totalVariation.restrict K) ∧
      Integrable f (mu.imPart.totalVariation.restrict K) := by
    apply integrable_add_measure.mp
    simpa only [variationControl,Measure.restrict_add] using hf
  simp only [finiteComplexIntegral,compactRestriction_re,compactRestriction_im,
    localSignedCompactRestriction_integral _ _ _ f hparts.1,
    localSignedCompactRestriction_integral _ _ _ f hparts.2]

theorem LocallyFiniteComplexMeasure.finiteComplexIntegral_eq_integral_of_support
    (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ→ℂ) (hf : Integrable f (mu.variationControl.restrict K))
    (hsupport : Function.support f⊆K) :
    finiteComplexIntegral (mu.compactRestriction K hK) f=mu.integral f := by
  have hz (x : ℝ) (hx : x∉K) : f x=0 := by
    by_contra h
    exact hx (hsupport h)
  rw [mu.finiteComplexIntegral_compactRestriction K hK f hf]
  simp only [setIntegral_eq_integral_of_forall_compl_eq_zero hz,integral]

theorem LocalVariationConvergence.tendsto_compact_test
    {seq : ℕ→LocallyFiniteComplexMeasure} {mu : LocallyFiniteComplexMeasure}
    (h : LocalVariationConvergence seq mu) (f : ℝ→ℂ)
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun n => (seq n).integral f) atTop (𝓝 (mu.integral f)) := by
  obtain ⟨x0,hC⟩ := hf.norm.exists_forall_ge_of_hasCompactSupport hs.norm
  have hint (nu : LocallyFiniteComplexMeasure) : Integrable f (nu.variationControl.restrict (tsupport f)) :=
    (hf.integrable_of_hasCompactSupport hs).integrableOn
  have heq (nu : LocallyFiniteComplexMeasure) :=
    nu.finiteComplexIntegral_eq_integral_of_support (tsupport f) hs f (hint nu) (subset_tsupport f)
  simpa only [heq] using h.tendsto_local_test (tsupport f) hs f hf.stronglyMeasurable
    ‖f x0‖ (norm_nonneg _) hC

/-!
Supporting continuation after the preserved compact-arithmetic,
compact-coherence and integral-compatibility candidates. The complete primary
`complex_local_measure_embedding_faithful` is intentionally NOT declared here:
uniform Schwartz tails and all global arithmetic consumers remain obligations.
-/

/-- The coordinate variation is a control within a factor two of the genuine
Euclidean variation on every compact restriction. Whole-line finiteness is
neither assumed nor inferred. -/
theorem LocallyFiniteComplexMeasure.variationControl_restrict_le_two
    (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    mu.variationControl.restrict K ≤
      mu.totalVariation.restrict K + mu.totalVariation.restrict K := by
  rw [LocallyFiniteComplexMeasure.variationControl,Measure.restrict_add,
    ←localSignedCompactRestriction_variation mu.rePart K hK,
    ←localSignedCompactRestriction_variation mu.imPart K hK,
    ←mu.compactRestriction_re K hK,←mu.compactRestriction_im K hK,
    mu.totalVariation_restrict_compact K hK]
  exact add_le_add (complexMeasure_re_variation_le (mu.compactRestriction K hK))
    (complexMeasure_im_variation_le (mu.compactRestriction K hK))

/-- In particular the implemented coordinate-growth domain is equivalent to
linear growth of the actual Euclidean complex variation. The reverse
implication pays the factor two rather than pretending the measures equal. -/
theorem LocallyFiniteComplexMeasure.hasLinearGrowth_iff_totalVariation
    (mu : LocallyFiniteComplexMeasure) :
    mu.HasLinearGrowth ↔ Zeta23.OPICA.LinearMassGrowth mu.totalVariation := by
  constructor
  · intro h
    exact h.mono mu.totalVariation_le_control
  · rintro ⟨C,hC,hbound⟩
    refine ⟨2*C,by positivity,?_⟩
    intro R hR
    have hle := mu.variationControl_restrict_le_two (Icc (-R) R) isCompact_Icc univ
    simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter,Measure.add_apply] at hle
    have hfinite : mu.totalVariation (Icc (-R) R) ≠ ∞ := isCompact_Icc.measure_lt_top.ne
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinite,hfinite⟩) hle
    rw [ENNReal.toReal_add hfinite hfinite] at hreal
    have hB := hbound R hR
    change (mu.totalVariation (Icc (-R) R)).toReal ≤ C*(1+R) at hB
    change (mu.variationControl (Icc (-R) R)).toReal ≤ (2*C)*(1+R)
    nlinarith

/-- Quantified compact-test error, in terms of the genuine compact complex
variation of the difference. This is not a statement about coordinate
cancellation or total variation on the whole line. -/
theorem LocallyFiniteComplexMeasure.compact_integral_difference_bound
    (mu nu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ → ℂ) (hf : Continuous f) (hs : Function.support f ⊆ K)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, ‖f x‖ ≤ M) :
    ‖mu.integral f - nu.integral f‖ ≤
      2*M*(mu.compactRestriction K hK - nu.compactRestriction K hK).variation.real univ := by
  let : IsFiniteMeasure (mu.variationControl.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : IsFiniteMeasure (nu.variationControl.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hm : Integrable f (mu.variationControl.restrict K) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall hbound)
  have hn : Integrable f (nu.variationControl.restrict K) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall hbound)
  rw [←mu.finiteComplexIntegral_eq_integral_of_support K hK f hm hs,
    ←nu.finiteComplexIntegral_eq_integral_of_support K hK f hn hs,
    ←finiteComplexIntegral_sub _ _ f hf.stronglyMeasurable M hbound]
  exact finiteComplexIntegral_norm_le _ f M hM hbound

/-- A finite-coordinate support restriction can be chosen before applying the
local-TV hypothesis. This explicit statement prevents a hidden uniform global
finite-mass premise from entering the compact convergence result. -/
theorem LocalVariationConvergence.tendsto_compact_test_with_error
    {seq : ℕ → LocallyFiniteComplexMeasure} {mu : LocallyFiniteComplexMeasure}
    (h : LocalVariationConvergence seq mu) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ → ℂ) (hf : Continuous f) (hs : Function.support f ⊆ K)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun n => (seq n).integral f) atTop (𝓝 (mu.integral f)) ∧
      ∀ n, ‖(seq n).integral f - mu.integral f‖ ≤
        2*M*((seq n).compactRestriction K hK-mu.compactRestriction K hK).variation.real univ := by
  have hb (n : ℕ) := (seq n).compact_integral_difference_bound mu K hK f hf hs M hM hbound
  refine ⟨?_,hb⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hb
    (by simpa using (h K hK).const_mul (2*M))


/-!
## Uniform local-variation to Schwartz convergence

UNCHECKED continuation at 9b6a9a3.  The common growth constant below is a
hypothesis about the actual variation measures, not the desired convergence.
The tail estimate is proved before passing to the limit.  Global finite mass
is never assumed.
-/

open scoped ENNReal NNReal
open Zeta23.OPICA

/-- A quantified growth budget for a particular positive measure. -/
def CommonLinearMassBound (C : ℝ) (μ : Measure ℝ) : Prop :=
  0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → μ.real (Icc (-R) R) ≤ C*(1+R)

lemma CommonLinearMassBound.linearGrowth {C : ℝ} {μ : Measure ℝ}
    (h : CommonLinearMassBound C μ) : LinearMassGrowth μ := ⟨C,h.1,h.2⟩

lemma CommonLinearMassBound.mono {C : ℝ} {μ ν : Measure ℝ}
    [IsLocallyFiniteMeasure μ] (h : CommonLinearMassBound C μ) (hle : ν ≤ μ) :
    CommonLinearMassBound C ν := by
  refine ⟨h.1,fun R hR => ?_⟩
  exact (ENNReal.toReal_mono isCompact_Icc.measure_lt_top.ne (hle _)).trans (h.2 R hR)

/-- Closed shells can overlap on boundaries.  The proof deliberately uses
subadditivity, not an unproved disjointness assertion for atomic measures. -/
def complexTailShell (R : ℝ) (n : ℕ) : Set ℝ :=
  Icc (-(R*(2:ℝ)^(n+1))) (R*(2:ℝ)^(n+1)) \
    Ioo (-(R*(2:ℝ)^n)) (R*(2:ℝ)^n)

lemma complexTailShell_compact (R : ℝ) (n : ℕ) : IsCompact (complexTailShell R n) :=
  isCompact_Icc.diff isOpen_Ioo

lemma complexTailShell_cover {R : ℝ} (hR : 0<R) :
    (⋃ n : ℕ, complexTailShell R n) = {x : ℝ | R ≤ |x|} := by
  ext x
  constructor
  · intro hmem
    obtain ⟨n,hn⟩ := mem_iUnion.mp hmem
    have hn' : x ∈ complexTailShell R n := hn
    have hlow : R*(2:ℝ)^n ≤ |x| := by
      by_contra h
      exact hn'.2 (abs_lt.mp (lt_of_not_ge h))
    exact (le_mul_of_one_le_right hR.le (one_le_pow₀ (by norm_num))).trans hlow
  · intro hx
    obtain ⟨n,hn,hnnext⟩ := exists_nat_pow_near
      ((le_div_iff₀ hR).mpr (by simpa using hx)) (by norm_num : (1:ℝ)<2)
    apply mem_iUnion.mpr
    refine ⟨n,?_,?_⟩
    · apply abs_le.mp
      have h := (div_lt_iff₀ hR).mp hnnext
      simpa only [mul_comm] using h.le
    · intro hsmall
      have h := (le_div_iff₀ hR).mp hn
      have h' := abs_lt.mpr hsmall
      nlinarith

lemma integral_norm_iUnion_le_tsum {μ : Measure ℝ} (s : ℕ→Set ℝ) (f : ℝ→ℂ)
    (hi : ∀ n, IntegrableOn f (s n) μ)
    (hs : Summable (fun n => ∫ x in s n, ‖f x‖ ∂μ)) :
    (∫ x in ⋃ n, s n, ‖f x‖ ∂μ) ≤ ∑' n, ∫ x in s n, ‖f x‖ ∂μ := by
  have hu := integrableOn_iUnion_of_summable_integral_norm hi hs
  apply (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg (fun n => integral_nonneg (fun _ => norm_nonneg _)))).mp
  rw [ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun _ => norm_nonneg _)) hs]
  rw [ofReal_integral_eq_lintegral_ofReal hu.norm
    (Eventually.of_forall (fun x => norm_nonneg (f x)))]
  simp_rw [ofReal_integral_eq_lintegral_ofReal (hi _).norm
    (Eventually.of_forall (fun x => norm_nonneg (f x)))]
  exact lintegral_iUnion_le s (fun x => ENNReal.ofReal ‖f x‖)

/-- Quantitative tail estimate derived from a common linear mass bound and
an actual cubic pointwise decay.  This remains valid for atoms on shell edges. -/
theorem common_linear_cubic_tail (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (C M R : ℝ) (hμ : CommonLinearMassBound C μ) (hM : 0≤M) (hR : 1≤R)
    (f : ℝ→ℂ) (hf : Continuous f)
    (hdecay : ∀ x, |x|^3*‖f x‖≤M) :
    IntegrableOn f {x : ℝ | R≤|x|} μ ∧
    (∫ x in {x : ℝ | R≤|x|}, ‖f x‖ ∂μ) ≤ 4*C*M/R^2 := by
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hi (n : ℕ) : IntegrableOn f (complexTailShell R n) μ :=
    hf.continuousOn.integrableOn_compact (complexTailShell_compact R n)
  have hbound (n : ℕ) :
      (∫ x in complexTailShell R n, ‖f x‖ ∂μ) ≤ (3*C*M/R^2)*(1/4:ℝ)^n := by
    have hRn : 0<R*(2:ℝ)^n := by positivity
    have hpoint (x : ℝ) (hx : x∈complexTailShell R n) :
        ‖f x‖ ≤ M/(R*(2:ℝ)^n)^3 := by
      have hlow : R*(2:ℝ)^n ≤ |x| := by
        by_contra h
        exact hx.2 (abs_lt.mp (lt_of_not_ge h))
      apply (le_div_iff₀ (by positivity)).mpr
      have h := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hRn.le hlow 3)
        (norm_nonneg (f x))).trans (hdecay x)
      simpa only [mul_comm] using h
    have hmass : μ.real (complexTailShell R n) ≤ 3*C*R*(2:ℝ)^n := by
      calc
        _ ≤ μ.real (Icc (-(R*(2:ℝ)^(n+1))) (R*(2:ℝ)^(n+1))) :=
          measureReal_mono (fun _ hx => hx.1) isCompact_Icc.measure_lt_top.ne
        _ ≤ C*(1+R*(2:ℝ)^(n+1)) := by
          simpa only [neg_mul] using hμ.2 (R*(2:ℝ)^(n+1)) (by positivity)
        _ ≤ _ := by
          have hp : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
          rw [pow_succ]
          nlinarith [hμ.1,mul_le_mul hR hp (by norm_num : (0:ℝ)≤1) (by positivity : (0:ℝ)≤R)]
    calc
      _ = ‖∫ x in complexTailShell R n, ‖f x‖ ∂μ‖ := by
        rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      _ ≤ (M/(R*(2:ℝ)^n)^3)*μ.real (complexTailShell R n) :=
        norm_setIntegral_le_of_norm_le_const (complexTailShell_compact R n).measure_lt_top
          (fun x hx => by simpa only [norm_norm] using hpoint x hx)
      _ ≤ (M/(R*(2:ℝ)^n)^3)*(3*C*R*(2:ℝ)^n) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by
        rw [div_pow,one_pow,mul_pow]
        have hp : (2:ℝ)^n≠0 := by positivity
        field_simp
        ring_nf
        rw [show (4:ℝ)=(2:ℝ)^2 by norm_num, ←pow_mul, Nat.mul_comm 2 n]
  have hsmajor : Summable (fun n : ℕ => (3*C*M/R^2)*(1/4:ℝ)^n) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)).mul_left _
  have hs : Summable (fun n => ∫ x in complexTailShell R n, ‖f x‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound hsmajor
  have hc := complexTailShell_cover hRp
  constructor
  · rw [←hc]
    exact integrableOn_iUnion_of_summable_integral_norm hi hs
  · rw [←hc]
    apply (integral_norm_iUnion_le_tsum (complexTailShell R) f hi hs).trans
    calc
      _ ≤ ∑' n : ℕ, (3*C*M/R^2)*(1/4:ℝ)^n := hs.tsum_le_tsum hbound hsmajor
      _ = 4*C*M/R^2 := by
        rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)]
        ring

lemma LocallyFiniteComplexMeasure.integrable_schwartz
    (μ : LocallyFiniteComplexMeasure) (hμ : μ.HasLinearGrowth) (f : SchwartzMap ℝ ℂ) :
    Integrable f μ.variationControl := by
  letI := hasTemperateGrowth_of_linear_growth μ.variationControl hμ
  exact f.integrable

lemma complexIntegral_norm_le_control (μ : LocallyFiniteComplexMeasure)
    (f : ℝ→ℂ) (hf : Integrable f μ.variationControl) :
    ‖μ.integral f‖ ≤ ∫ x, ‖f x‖ ∂μ.variationControl := by
  have hp := integrable_add_measure.mp hf
  have hr := integrable_add_measure.mp hp.1
  have hi := integrable_add_measure.mp hp.2
  unfold LocallyFiniteComplexMeasure.integral LocallyFiniteComplexMeasure.variationControl
  rw [integral_add_measure hp.1.norm hp.2.norm]
  simp only [LocallyFiniteSignedMeasure.totalVariation]
  rw [integral_add_measure hr.1.norm hr.2.norm,
    integral_add_measure hi.1.norm hi.2.norm]
  calc
    _ ≤ ‖(∫ x, f x ∂μ.rePart.positive)-(∫ x, f x ∂μ.rePart.negative)‖+
        ‖I*((∫ x, f x ∂μ.imPart.positive)-(∫ x, f x ∂μ.imPart.negative))‖ := norm_add_le _ _
    _ ≤ (‖∫ x, f x ∂μ.rePart.positive‖+‖∫ x, f x ∂μ.rePart.negative‖)+
        (‖∫ x, f x ∂μ.imPart.positive‖+‖∫ x, f x ∂μ.imPart.negative‖) := by
      simp only [norm_mul,Complex.norm_I,one_mul]
      exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ ≤ _ := add_le_add (add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _))
      (add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _))

lemma complexIntegral_add_test (μ : LocallyFiniteComplexMeasure) (f g : ℝ→ℂ)
    (hf : Integrable f μ.variationControl) (hg : Integrable g μ.variationControl) :
    μ.integral (fun x => f x+g x)=μ.integral f+μ.integral g := by
  have hfr := integrable_add_measure.mp (integrable_add_measure.mp hf).1
  have hfi := integrable_add_measure.mp (integrable_add_measure.mp hf).2
  have hgr := integrable_add_measure.mp (integrable_add_measure.mp hg).1
  have hgi := integrable_add_measure.mp (integrable_add_measure.mp hg).2
  simp only [LocallyFiniteComplexMeasure.integral,integral_add hfr.1 hgr.1,
    integral_add hfr.2 hgr.2,integral_add hfi.1 hgi.1,integral_add hfi.2 hgi.2]
  ring

lemma complexIntegral_cutoff_error (μ : LocallyFiniteComplexMeasure)
    (C M R : ℝ) (hμ : CommonLinearMassBound C μ.variationControl) (hM : 0≤M)
    (hR : 1≤R) (f : SchwartzMap ℝ ℂ)
    (hdecay : ∀ x, |x|^3*‖f x‖≤M) :
    ‖μ.integral f-finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f‖
      ≤ 4*C*M/R^2 := by
  let K : Set ℝ := Icc (-R) R
  have hi := μ.integrable_schwartz hμ.linearGrowth f
  have hKf : Integrable (K.indicator (fun x => f x)) μ.variationControl :=
    hi.indicator (show MeasurableSet K from measurableSet_Icc)
  have hKcf : Integrable (Kᶜ.indicator (fun x => f x)) μ.variationControl :=
    hi.indicator (show MeasurableSet Kᶜ from measurableSet_Icc.compl)
  have hsplit : (fun x : ℝ => K.indicator (fun y => f y) x+
      Kᶜ.indicator (fun y => f y) x) = f := by
    funext x
    by_cases hx : x∈K <;> simp [hx]
  have hlocal : μ.integral (K.indicator (fun y => f y))=
      finiteComplexIntegral (μ.compactRestriction K isCompact_Icc) f := by
    rw [μ.finiteComplexIntegral_compactRestriction K isCompact_Icc f hi.integrableOn]
    simp only [LocallyFiniteComplexMeasure.integral,
      integral_indicator (show MeasurableSet K from measurableSet_Icc)]
  have heq := complexIntegral_add_test μ _ _ hKf hKcf
  rw [hsplit,hlocal] at heq
  rw [heq,add_sub_cancel_left]
  apply (complexIntegral_norm_le_control μ _ hKcf).trans
  have htail := (common_linear_cubic_tail μ.variationControl C M R hμ hM hR f
    f.continuous hdecay).2
  have hsub : Kᶜ ⊆ {x : ℝ | R≤|x|} := by
    intro x hx
    by_contra h
    exact hx (abs_le.mp (lt_of_not_ge h).le)
  calc
    (∫ x, ‖Kᶜ.indicator (fun y => f y) x‖ ∂μ.variationControl)
        = ∫ x in Kᶜ, ‖f x‖ ∂μ.variationControl := by
      rw [←integral_indicator (show MeasurableSet Kᶜ from measurableSet_Icc.compl)]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x∈K <;> simp [hx]
    _ ≤ ∫ x in {x : ℝ | R≤|x|}, ‖f x‖ ∂μ.variationControl :=
      setIntegral_mono_set hi.norm.integrableOn (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (Filter.Eventually.of_forall hsub)
    _ ≤ _ := htail

/-- Local convergence plus ONE common growth budget yields convergence on
all Schwartz tests.  The tails are not inserted as an extra hypothesis. -/
theorem LocalVariationConvergence.tendsto_schwartz_common_growth
    {seq : ℕ→LocallyFiniteComplexMeasure} {μ : LocallyFiniteComplexMeasure}
    (hlocal : LocalVariationConvergence seq μ) (C : ℝ)
    (hseq : ∀ n, CommonLinearMassBound C (seq n).variationControl)
    (hμ : CommonLinearMassBound C μ.variationControl) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (seq n).integral f) atTop (𝓝 (μ.integral f)) := by
  obtain ⟨M,hM,hdecay⟩ := f.decay 3 0
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hdecay
  obtain ⟨B,hB,hbound⟩ := f.decay 0 0
  simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero] at hbound
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have htail : Tendsto (fun R : ℝ => 8*C*M/R^2) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨R,hR,hs⟩ : ∃ R : ℝ, 1≤R ∧ 8*C*M/R^2<ε/2 := by
    have he := htail.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨R,hR,hs⟩ := (eventually_ge_atTop (1:ℝ)).and he |>.exists
    exact ⟨R,hR,hs⟩
  have hc := hlocal.tendsto_local_test (Icc (-R) R) isCompact_Icc f
    f.continuous.stronglyMeasurable B hB.le hbound
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hc (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have h1 := complexIntegral_cutoff_error (seq n) C M R (hseq n) hM.le hR f hdecay
  have h2 := complexIntegral_cutoff_error μ C M R hμ hM.le hR f hdecay
  have h3 := hN n hn
  rw [dist_eq_norm] at h3 ⊢
  have htri : ‖(seq n).integral f-μ.integral f‖ ≤
      ‖(seq n).integral f-finiteComplexIntegral ((seq n).compactRestriction (Icc (-R) R) isCompact_Icc) f‖+
      ‖finiteComplexIntegral ((seq n).compactRestriction (Icc (-R) R) isCompact_Icc) f-
        finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f‖+
      ‖μ.integral f-finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f‖ := by
    have h := norm_add_le
      ((seq n).integral f-finiteComplexIntegral ((seq n).compactRestriction (Icc (-R) R) isCompact_Icc) f)
      ((finiteComplexIntegral ((seq n).compactRestriction (Icc (-R) R) isCompact_Icc) f-
        finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f)+
        (finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f-μ.integral f))
    have h' := norm_add_le
      (finiteComplexIntegral ((seq n).compactRestriction (Icc (-R) R) isCompact_Icc) f-
        finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f)
      (finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f-μ.integral f)
    rw [norm_sub_rev (finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f)] at h'
    have he : ((seq n).integral f-finiteComplexIntegral ((seq n).compactRestriction (Icc (-R) R) isCompact_Icc) f)+
      ((finiteComplexIntegral ((seq n).compactRestriction (Icc (-R) R) isCompact_Icc) f-
        finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f)+
        (finiteComplexIntegral (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f-μ.integral f))=
      (seq n).integral f-μ.integral f := by ring
    rw [he] at h
    linarith
  have he : 8*C*M/R^2 = 2*(4*C*M/R^2) := by ring
  rw [he] at hs
  linarith

lemma localJordanAdd_totalVariation_le (μ ν : LocallyFiniteSignedMeasure) :
    (localJordanAdd μ ν).totalVariation≤μ.totalVariation+ν.totalVariation := by
  exact (localJordanDifference_variation_le _ _).trans_eq (by
    simp only [LocallyFiniteSignedMeasure.totalVariation]; abel)

lemma localJordanScale_totalVariation_le (a : ℝ) (μ : LocallyFiniteSignedMeasure) :
    (localJordanScale a μ).totalVariation ≤ ENNReal.ofReal |a| • μ.totalVariation := by
  apply (localJordanDifference_variation_le _ _).trans_eq
  rw [LocallyFiniteSignedMeasure.totalVariation,smul_add]
  ext s hs
  simp only [Measure.add_apply,Measure.smul_apply,NNReal.smul_def,ENNReal.smul_def]
  have ha : (Real.toNNReal a:ℝ≥0∞)+(Real.toNNReal (-a):ℝ≥0∞)=ENNReal.ofReal |a| := by
    rcases le_total 0 a with ha|ha
    · simp [Real.toNNReal_of_nonpos (neg_nonpos.mpr ha),abs_of_nonneg ha, ENNReal.ofReal]
    · simp [Real.toNNReal_of_nonpos ha,abs_of_nonpos ha, ENNReal.ofReal]
  rw [←ha]
  ring

lemma LocallyFiniteComplexMeasure.add_control_le (μ ν : LocallyFiniteComplexMeasure) :
    (μ.add ν).variationControl≤μ.variationControl+ν.variationControl := by
  apply (add_le_add (localJordanAdd_totalVariation_le _ _) (localJordanAdd_totalVariation_le _ _)).trans_eq
  simp only [variationControl]
  abel

lemma LocallyFiniteComplexMeasure.scale_control_le (μ : LocallyFiniteComplexMeasure) (c : ℂ) :
    (μ.scale c).variationControl ≤ ENNReal.ofReal (|c.re|+|c.im|) • μ.variationControl := by
  apply (add_le_add
    ((localJordanAdd_totalVariation_le _ _).trans
      (add_le_add (localJordanScale_totalVariation_le _ _) (localJordanScale_totalVariation_le _ _)))
    ((localJordanAdd_totalVariation_le _ _).trans
      (add_le_add (localJordanScale_totalVariation_le _ _) (localJordanScale_totalVariation_le _ _)))).trans_eq
  simp only [variationControl,abs_neg,ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),add_smul,smul_add]
  abel

lemma LocallyFiniteComplexMeasure.hasLinearGrowth_add (μ ν : LocallyFiniteComplexMeasure)
    (hμ : μ.HasLinearGrowth) (hν : ν.HasLinearGrowth) : (μ.add ν).HasLinearGrowth := by
  obtain ⟨A,hA,hAb⟩ := hμ
  obtain ⟨B,hB,hBb⟩ := hν
  refine ⟨A+B,add_nonneg hA hB,fun R hR => ?_⟩
  have hmfin : μ.variationControl (Icc (-R) R)≠∞ := isCompact_Icc.measure_lt_top.ne
  have hnfin : ν.variationControl (Icc (-R) R)≠∞ := isCompact_Icc.measure_lt_top.ne
  have hsumfin : (μ.variationControl+ν.variationControl) (Icc (-R) R)≠∞ := by
    rw [Measure.add_apply]
    exact ENNReal.add_ne_top.mpr ⟨hmfin,hnfin⟩
  have h := ENNReal.toReal_mono hsumfin (μ.add_control_le ν (Icc (-R) R))
  rw [Measure.add_apply,ENNReal.toReal_add hmfin hnfin] at h
  have ha := hAb R hR
  have hb := hBb R hR
  change ((μ.add ν).variationControl (Icc (-R) R)).toReal≤_ at h ⊢
  change (μ.variationControl (Icc (-R) R)).toReal≤_ at ha
  change (ν.variationControl (Icc (-R) R)).toReal≤_ at hb
  nlinarith

lemma LocallyFiniteComplexMeasure.hasLinearGrowth_scale (μ : LocallyFiniteComplexMeasure)
    (hμ : μ.HasLinearGrowth) (c : ℂ) : (μ.scale c).HasLinearGrowth := by
  obtain ⟨A,hA,hAb⟩ := hμ
  let B : ℝ := |c.re|+|c.im|
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨B*A,mul_nonneg hB hA,fun R hR => ?_⟩
  have hle := μ.scale_control_le c (Icc (-R) R)
  rw [Measure.smul_apply,smul_eq_mul] at hle
  have hfin : ENNReal.ofReal B*μ.variationControl (Icc (-R) R)≠∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top isCompact_Icc.measure_lt_top.ne
  have hh := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hB] at hh
  have ha := hAb R hR
  change (μ.variationControl (Icc (-R) R)).toReal≤_ at ha
  change ((μ.scale c).variationControl (Icc (-R) R)).toReal≤_
  nlinarith

/-- Realification is an actual inverse to taking the real part of the
embedded distribution.  It retains the parent canonical Jordan carrier. -/
def realifyComplexDistribution (T : TemperedDistribution ℝ ℂ) (f : SchwartzMap ℝ ℂ) : ℂ :=
  (T f+starRingEnd ℂ (T (complexSchwartzConj f)))/2

lemma LocallyFiniteComplexMeasure.realify_distribution (μ : LocallyFiniteComplexMeasure)
    (hμ : μ.HasLinearGrowth) (f : SchwartzMap ℝ ℂ) :
    realifyComplexDistribution (μ.distributionOfLinearGrowth hμ) f =
      μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth hμ) f := by
  unfold realifyComplexDistribution distributionOfLinearGrowth
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    realJordan_distribution_conj,map_add,map_mul,Complex.conj_I,Complex.conj_conj]
  field_simp
  ring

/-- Full primary interface: genuine compact restrictions and variation,
faithful growth-domain distribution, canonical realification and actual
common-growth Schwartz convergence.  No native convergence is a field in
an input packet. -/
theorem complex_local_measure_embedding_faithful :
    (∀ μ : LocallyFiniteComplexMeasure, μ.totalVariation≤μ.variationControl ∧
      (μ.HasLinearGrowth ↔ LinearMassGrowth μ.totalVariation)) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ K L : Set ℝ, ∀ hK : IsCompact K, ∀ hL : IsCompact L,
      (μ.compactRestriction K hK).restrict L=μ.compactRestriction (K∩L) (hK.inter_right hL.isClosed)) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ K : Set ℝ, ∀ hK : IsCompact K,
      μ.totalVariation.restrict K=(μ.compactRestriction K hK).variation) ∧
    (∀ μ ν : LocallyFiniteComplexMeasure, ∀ c : ℂ, ∀ K : Set ℝ, ∀ hK : IsCompact K,
      (μ.add ν).compactRestriction K hK=μ.compactRestriction K hK+ν.compactRestriction K hK ∧
      (μ.scale c).compactRestriction K hK=c • μ.compactRestriction K hK) ∧
    Function.Injective (fun μ : {μ : LocallyFiniteComplexMeasure // μ.HasLinearGrowth} =>
      μ.val.distributionOfLinearGrowth μ.property) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ hμ : μ.HasLinearGrowth, ∀ f : SchwartzMap ℝ ℂ,
      μ.distributionOfLinearGrowth hμ f=μ.integral f ∧
      realifyComplexDistribution (μ.distributionOfLinearGrowth hμ) f=
        μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth hμ) f) ∧
    (∀ seq : ℕ→LocallyFiniteComplexMeasure, ∀ μ : LocallyFiniteComplexMeasure,
      LocalVariationConvergence seq μ → ∀ f : ℝ→ℂ,
      Continuous f → HasCompactSupport f →
      Tendsto (fun n => (seq n).integral f) atTop (𝓝 (μ.integral f))) ∧
    (∀ seq : ℕ→LocallyFiniteComplexMeasure, ∀ μ : LocallyFiniteComplexMeasure,
      LocalVariationConvergence seq μ → ∀ C : ℝ,
      (∀ n, CommonLinearMassBound C (seq n).variationControl) →
      CommonLinearMassBound C μ.variationControl → ∀ f : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (seq n).integral f) atTop (𝓝 (μ.integral f))) := by
  refine ⟨fun μ => ⟨μ.totalVariation_le_control,μ.hasLinearGrowth_iff_totalVariation⟩,
    fun μ K L hK hL => μ.compactRestriction_restrict K L hK hL,
    fun μ K hK => μ.totalVariation_restrict_compact K hK,
    fun μ ν c K hK => ⟨μ.compactRestriction_add ν K hK,μ.compactRestriction_scale c K hK⟩,
    LocallyFiniteComplexMeasure.distributionOfLinearGrowth_injective,
    fun μ hμ f => ⟨μ.distributionOfLinearGrowth_apply hμ f,μ.realify_distribution hμ f⟩,
    fun seq μ h f hf hc => h.tendsto_compact_test f hf hc,
    fun seq μ h C hs hm f => h.tendsto_schwartz_common_growth C hs hm f⟩

end Zeta23.OPICAFollowup
