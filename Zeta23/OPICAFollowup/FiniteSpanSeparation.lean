import Zeta23.OPICAFollowup.ConfluentProfiles
import Zeta23.OPICA.SignedHeatSeparator
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Actual finite realified zero-jet measures and their sharp-gap restriction.
The original R2-H2b domain is finite combinations of the actual normalized
jets below each actual zero multiplicity. No measure status, growth, gap,
self-duality, positivity conclusion or independent-coefficient conclusion
is assumed in a packet. The independent real-basis clause quantifies actual
basis vectors in this span and retains independence explicitly. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform ENNReal NNReal

namespace Zeta23.OPICAFollowup.FiniteSpan
open Zeta23.OPICA

def zeroJordan : LocallyFiniteSignedMeasure :=
  ⟨0, 0, inferInstance, inferInstance, Measure.MutuallySingular.zero_left⟩

def zeroComplex : LocallyFiniteComplexMeasure := ⟨zeroJordan, zeroJordan⟩

lemma zeroComplex_growth : zeroComplex.HasLinearGrowth := by
  refine ⟨0, le_rfl, fun R hR => ?_⟩
  simp [zeroComplex, zeroJordan, LocallyFiniteComplexMeasure.variationControl,
    LocallyFiniteSignedMeasure.totalVariation, Measure.real]

lemma zeroComplex_integral (f : ℝ → ℂ) : zeroComplex.integral f = 0 := by
  simp [zeroComplex, zeroJordan, LocallyFiniteComplexMeasure.integral]

lemma signed_integral_add (μ ν : LocallyFiniteSignedMeasure)
    (f : ℝ → ℂ) (hμp : Integrable f μ.positive) (hμn : Integrable f μ.negative)
    (hνp : Integrable f ν.positive) (hνn : Integrable f ν.negative) :
    (∫ x, f x ∂(localJordanAdd μ ν).positive) -
        (∫ x, f x ∂(localJordanAdd μ ν).negative) =
      ((∫ x, f x ∂μ.positive) - ∫ x, f x ∂μ.negative) +
      ((∫ x, f x ∂ν.positive) - ∫ x, f x ∂ν.negative) := by
  rw [localJordanAdd, localJordanDifference_integral _ _ f
    (integrable_add_measure.mpr ⟨hμp,hνp⟩) (integrable_add_measure.mpr ⟨hμn,hνn⟩),
    integral_add_measure hμp hνp, integral_add_measure hμn hνn]
  ring

lemma signed_integral_scale (a : ℝ) (μ : LocallyFiniteSignedMeasure)
    (f : ℝ → ℂ) (hμp : Integrable f μ.positive) (hμn : Integrable f μ.negative) :
    (∫ x, f x ∂(localJordanScale a μ).positive) -
        (∫ x, f x ∂(localJordanScale a μ).negative) =
      (a : ℂ) * ((∫ x, f x ∂μ.positive) - ∫ x, f x ∂μ.negative) := by
  rw [localJordanScale]
  have hpp : Integrable f (Real.toNNReal a • μ.positive) :=
    hμp.smul_measure (c := (Real.toNNReal a : ℝ≥0∞)) ENNReal.coe_ne_top
  have hpn : Integrable f (Real.toNNReal a • μ.negative) :=
    hμn.smul_measure (c := (Real.toNNReal a : ℝ≥0∞)) ENNReal.coe_ne_top
  have hnp : Integrable f (Real.toNNReal (-a) • μ.positive) :=
    hμp.smul_measure (c := (Real.toNNReal (-a) : ℝ≥0∞)) ENNReal.coe_ne_top
  have hnn : Integrable f (Real.toNNReal (-a) • μ.negative) :=
    hμn.smul_measure (c := (Real.toNNReal (-a) : ℝ≥0∞)) ENNReal.coe_ne_top
  rw [localJordanDifference_integral _ _ f
    (integrable_add_measure.mpr ⟨hpp,hnn⟩)
    (integrable_add_measure.mpr ⟨hpn,hnp⟩),
    integral_add_measure hpp hnn, integral_add_measure hpn hnp]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have ha : (Real.toNNReal a : ℝ) - (Real.toNNReal (-a) : ℝ) = a := by
    rw [Real.coe_toNNReal',Real.coe_toNNReal']
    rcases le_total 0 a with h|h
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
  have hac : ((Real.toNNReal a : ℝ) : ℂ) - ((Real.toNNReal (-a) : ℝ) : ℂ) = (a : ℂ) := by
    exact_mod_cast ha
  rw [←hac]
  ring

lemma signed_scale_integrable_parts (a : ℝ) (μ : LocallyFiniteSignedMeasure)
    (f : ℝ → ℂ) (hp : Integrable f μ.positive) (hn : Integrable f μ.negative) :
    Integrable f (localJordanScale a μ).positive ∧
      Integrable f (localJordanScale a μ).negative := by
  have h : Integrable f (ENNReal.ofReal |a| • μ.totalVariation) :=
    (integrable_add_measure.mpr ⟨hp,hn⟩).smul_measure ENNReal.ofReal_ne_top
  have h' := h.mono_measure (localJordanScale_totalVariation_le a μ)
  exact integrable_add_measure.mp h'

lemma complex_integral_add (μ ν : LocallyFiniteComplexMeasure)
    (hμ : μ.HasLinearGrowth) (hν : ν.HasLinearGrowth) (f : 𝓢(ℝ, ℂ)) :
    (μ.add ν).integral f = μ.integral f + ν.integral f := by
  obtain ⟨hr,hi⟩ := integrable_add_measure.mp (μ.integrable_schwartz hμ f)
  obtain ⟨hmp,hmn⟩ := integrable_add_measure.mp hr
  obtain ⟨hmip,hmin⟩ := integrable_add_measure.mp hi
  obtain ⟨hr,hi⟩ := integrable_add_measure.mp (ν.integrable_schwartz hν f)
  obtain ⟨hnp,hnn⟩ := integrable_add_measure.mp hr
  obtain ⟨hnip,hnin⟩ := integrable_add_measure.mp hi
  dsimp only [LocallyFiniteComplexMeasure.add, LocallyFiniteComplexMeasure.integral]
  rw [signed_integral_add _ _ _ hmp hmn hnp hnn,
    signed_integral_add _ _ _ hmip hmin hnip hnin]
  ring

lemma complex_integral_scale (μ : LocallyFiniteComplexMeasure)
    (hμ : μ.HasLinearGrowth) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    (μ.scale c).integral f = c * μ.integral f := by
  obtain ⟨hr,hi⟩ := integrable_add_measure.mp (μ.integrable_schwartz hμ f)
  obtain ⟨hrp,hrn⟩ := integrable_add_measure.mp hr
  obtain ⟨hip,hin⟩ := integrable_add_measure.mp hi
  have hrr := signed_scale_integrable_parts c.re μ.rePart f hrp hrn
  have hri := signed_scale_integrable_parts (-c.im) μ.imPart f hip hin
  have hir := signed_scale_integrable_parts c.im μ.rePart f hrp hrn
  have hii := signed_scale_integrable_parts c.re μ.imPart f hip hin
  dsimp only [LocallyFiniteComplexMeasure.scale, LocallyFiniteComplexMeasure.integral]
  rw [signed_integral_add _ _ _ hrr.1 hrr.2 hri.1 hri.2,
    signed_integral_add _ _ _ hir.1 hir.2 hii.1 hii.2,
    signed_integral_scale _ _ _ hrp hrn, signed_integral_scale _ _ _ hip hin,
    signed_integral_scale _ _ _ hrp hrn, signed_integral_scale _ _ _ hip hin]
  simp only [Complex.ofReal_neg]
  conv_rhs => rw [←Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma imPart_fourierSelfdual_of_complex (μ : LocallyFiniteComplexMeasure) (h : μ.HasLinearGrowth)
    (hself : ∀ φ : 𝓢(ℝ, ℂ), μ.integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = μ.integral φ)
    (heven : ∀ φ : 𝓢(ℝ, ℂ), μ.integral (schwartzReflect φ) = μ.integral φ) :
    𝓕 (μ.imPart.distributionOfLinearGrowth (μ.im_hasLinearGrowth h)) =
      μ.imPart.distributionOfLinearGrowth (μ.im_hasLinearGrowth h) := by
  have hr := rePart_fourierSelfdual_of_complex μ h hself heven
  ext φ
  have hrφ := congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) hr
  have hcφ := hself φ
  change μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth h) (𝓕 φ) +
      I * μ.imPart.distributionOfLinearGrowth (μ.im_hasLinearGrowth h) (𝓕 φ) =
    μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth h) φ +
      I * μ.imPart.distributionOfLinearGrowth (μ.im_hasLinearGrowth h) φ at hcφ
  change μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth h) (𝓕 φ) =
    μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth h) φ at hrφ
  change μ.imPart.distributionOfLinearGrowth (μ.im_hasLinearGrowth h) (𝓕 φ) =
    μ.imPart.distributionOfLinearGrowth (μ.im_hasLinearGrowth h) φ
  apply mul_left_cancel₀ I_ne_zero
  exact add_left_cancel (hrφ ▸ hcφ)

/-- Coefficient, actual zeta zero, and normalized kappa-jet order. -/
abbrev JetDatum := ℂ × ℂ × ℕ

def ValidJet (j : JetDatum) : Prop :=
  riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
    j.2.2 < zeroJetOrder j.2.1

def actualZeroJetSum : List JetDatum → LocallyFiniteComplexMeasure
  | [] => zeroComplex
  | j :: rest => ((normalizedZeroMeasureJet j.2.1 j.2.2).scale j.1).add (actualZeroJetSum rest)

/-- The canonical real Jordan measure of a finite sum of genuine complex jets.
Taking Re(c nu) includes arbitrary real/imaginary coefficient combinations. -/
def zeroJetRealSpan (data : List JetDatum) : LocallyFiniteSignedMeasure :=
  (actualZeroJetSum data).rePart

lemma actualZeroJetSum_growth (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j) :
    (actualZeroJetSum data).HasLinearGrowth := by
  induction data with
  | nil => exact zeroComplex_growth
  | cons j rest ih =>
    obtain ⟨hz,h0,h1,hk⟩ := h j (by simp)
    exact LocallyFiniteComplexMeasure.hasLinearGrowth_add _ _
      (LocallyFiniteComplexMeasure.hasLinearGrowth_scale _
        (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz) hk) j.1)
      (ih (fun z hz => h z (by simp [hz])))

lemma actualZeroJetSum_gap (data : List JetDatum) :
    (actualZeroJetSum data).variationControl (Ioo (-1) 1) = 0 := by
  induction data with
  | nil => simp [actualZeroJetSum, zeroComplex, zeroJordan,
      LocallyFiniteComplexMeasure.variationControl, LocallyFiniteSignedMeasure.totalVariation]
  | cons j rest ih =>
    have hs := (normalizedZeroMeasureJet j.2.1 j.2.2).scale_control_le j.1 (Ioo (-1) 1)
    rw [Measure.smul_apply, (normalizedZeroMeasureJet_gap (ρ := j.2.1) j.2.2).1,
      smul_zero] at hs
    have ha := LocallyFiniteComplexMeasure.add_control_le
      ((normalizedZeroMeasureJet j.2.1 j.2.2).scale j.1) (actualZeroJetSum rest) (Ioo (-1) 1)
    rw [Measure.add_apply, ih, add_zero] at ha
    exact le_antisymm (ha.trans hs) zero_le

lemma actualZeroJetSum_fourier (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j)
    (φ : 𝓢(ℝ, ℂ)) :
    (actualZeroJetSum data).integral (𝓕 φ : 𝓢(ℝ, ℂ)) = (actualZeroJetSum data).integral φ := by
  induction data with
  | nil => rw [actualZeroJetSum, zeroComplex_integral, zeroComplex_integral]
  | cons j rest ih =>
    obtain ⟨hz,h0,h1,hk⟩ := h j (by simp)
    have hj := normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz) hk
    have ht : ∀ z ∈ rest, ValidJet z := fun z hz => h z (by simp [hz])
    have hs := LocallyFiniteComplexMeasure.hasLinearGrowth_scale _ hj j.1
    rw [actualZeroJetSum, complex_integral_add _ _ hs (actualZeroJetSum_growth rest ht),
      complex_integral_add _ _ hs (actualZeroJetSum_growth rest ht),
      complex_integral_scale _ hj, complex_integral_scale _ hj,
      normalizedZeroMeasureJet_fourier h0 h1 (zero_ne_half hz) hk, ih ht]

lemma actualZeroJetSum_reflect (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j)
    (φ : 𝓢(ℝ, ℂ)) :
    (actualZeroJetSum data).integral (schwartzReflect φ) = (actualZeroJetSum data).integral φ := by
  induction data with
  | nil => rw [actualZeroJetSum, zeroComplex_integral, zeroComplex_integral]
  | cons j rest ih =>
    obtain ⟨hz,h0,h1,hk⟩ := h j (by simp)
    have hj := normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz) hk
    have ht : ∀ z ∈ rest, ValidJet z := fun z hz => h z (by simp [hz])
    have hs := LocallyFiniteComplexMeasure.hasLinearGrowth_scale _ hj j.1
    rw [actualZeroJetSum, complex_integral_add _ _ hs (actualZeroJetSum_growth rest ht),
      complex_integral_add _ _ hs (actualZeroJetSum_growth rest ht),
      complex_integral_scale _ hj, complex_integral_scale _ hj,
      normalizedZeroMeasureJet_reflect h0 h1 (zero_ne_half hz), ih ht]

lemma zeroJetRealSpan_growth (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j) :
    (zeroJetRealSpan data).HasLinearGrowth :=
  (actualZeroJetSum data).re_hasLinearGrowth (actualZeroJetSum_growth data h)

lemma zeroJetRealSpan_gap (data : List JetDatum) : (zeroJetRealSpan data).HasUnitGap := by
  have h := actualZeroJetSum_gap data
  rw [LocallyFiniteComplexMeasure.variationControl, Measure.add_apply] at h
  have hr := (add_eq_zero.mp h).1
  rw [LocallyFiniteSignedMeasure.totalVariation, Measure.add_apply] at hr
  exact add_eq_zero.mp hr

lemma zeroJetRealSpan_selfdual (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j) :
    (zeroJetRealSpan data).FourierSelfdual (zeroJetRealSpan_growth data h) :=
  rePart_fourierSelfdual_of_complex _ (actualZeroJetSum_growth data h)
    (actualZeroJetSum_fourier data h) (actualZeroJetSum_reflect data h)

/-- Actual finite zero-jet measures cannot enter the off-lattice positive cone.
All analytic hypotheses of the parent separator are proved above from actual jets. -/
theorem finite_zero_span_positive_only_zero (data : List JetDatum)
    (h : ∀ j ∈ data, ValidJet j) (hoff : (zeroJetRealSpan data).OffLatticeNonnegative) :
    (zeroJetRealSpan data).positive = 0 ∧ (zeroJetRealSpan data).negative = 0 := by
  exact signed_sharp_gap_separator _ (zeroJetRealSpan_growth data h)
    (zeroJetRealSpan_selfdual data h) (zeroJetRealSpan_gap data) hoff

lemma actualZeroJetSum_integral (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j)
    (φ : 𝓢(ℝ, ℂ)) :
    (actualZeroJetSum data).integral φ =
      (data.map (fun j => j.1 * (normalizedZeroMeasureJet j.2.1 j.2.2).integral φ)).sum := by
  induction data with
  | nil => simp [actualZeroJetSum, zeroComplex_integral]
  | cons j rest ih =>
    obtain ⟨hz,h0,h1,hk⟩ := h j (by simp)
    have hj := normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz) hk
    have ht : ∀ z ∈ rest, ValidJet z := fun z hz => h z (by simp [hz])
    simp only [actualZeroJetSum, List.map_cons, List.sum_cons]
    rw [complex_integral_add _ _ (LocallyFiniteComplexMeasure.hasLinearGrowth_scale _ hj j.1)
      (actualZeroJetSum_growth rest ht), complex_integral_scale _ hj, ih ht]

lemma zeroJetRealSpan_distribution (data : List JetDatum) (h : ∀ j ∈ data, ValidJet j)
    (φ : 𝓢(ℝ, ℂ)) :
    (zeroJetRealSpan data).distributionOfLinearGrowth (zeroJetRealSpan_growth data h) φ =
      ((data.map (fun j => j.1 * (normalizedZeroMeasureJet j.2.1 j.2.2).integral φ)).sum +
        starRingEnd ℂ ((data.map (fun j => j.1 *
          (normalizedZeroMeasureJet j.2.1 j.2.2).integral (complexSchwartzConj φ))).sum)) / 2 := by
  change ((actualZeroJetSum data).rePart.distributionOfLinearGrowth
    ((actualZeroJetSum data).re_hasLinearGrowth (actualZeroJetSum_growth data h))) φ = _
  rw [←(actualZeroJetSum data).realify_distribution (actualZeroJetSum_growth data h) φ]
  simp only [realifyComplexDistribution, LocallyFiniteComplexMeasure.distributionOfLinearGrowth_apply,
    actualZeroJetSum_integral data h]

def realCoefficientData {n : ℕ} (basis : Fin n → JetDatum) (a : Fin n → ℝ) : List JetDatum :=
  List.ofFn (fun i => ((a i : ℂ) * (basis i).1, (basis i).2.1, (basis i).2.2))

lemma realCoefficientData_valid {n : ℕ} (basis : Fin n → JetDatum)
    (h : ∀ i, ValidJet (basis i)) (a : Fin n → ℝ) :
    ∀ j ∈ realCoefficientData basis a, ValidJet j := by
  intro j hj
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
  exact h i

lemma valid_singleton (j : JetDatum) (h : ValidJet j) : ∀ z ∈ [j], ValidJet z := by
  intro z hz
  rcases List.mem_singleton.mp hz with rfl
  exact h

lemma realCoefficientData_distribution {n : ℕ} (basis : Fin n → JetDatum)
    (h : ∀ i, ValidJet (basis i)) (a : Fin n → ℝ) :
    (zeroJetRealSpan (realCoefficientData basis a)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (realCoefficientData_valid basis h a)) =
      ∑ i, a i • (zeroJetRealSpan [basis i]).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (valid_singleton _ (h i))) := by
  ext φ
  rw [zeroJetRealSpan_distribution _ (realCoefficientData_valid basis h a)]
  simp only [realCoefficientData, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    map_sum, map_mul, Complex.conj_ofReal, sum_apply, smul_apply, Complex.real_smul]
  rw [←Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [zeroJetRealSpan_distribution [basis i] (valid_singleton _ (h i))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, map_mul]
  ring

theorem independent_real_basis_coefficients_zero {n : ℕ} (basis : Fin n → JetDatum)
    (h : ∀ i, ValidJet (basis i))
    (hind : LinearIndependent ℝ (fun i => (zeroJetRealSpan [basis i]).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (valid_singleton _ (h i)))))
    (a : Fin n → ℝ)
    (hoff : (zeroJetRealSpan (realCoefficientData basis a)).OffLatticeNonnegative) : a = 0 := by
  have hz := finite_zero_span_positive_only_zero _ (realCoefficientData_valid basis h a) hoff
  have hdist : (zeroJetRealSpan (realCoefficientData basis a)).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (realCoefficientData_valid basis h a)) = 0 := by
    ext φ
    rw [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply, hz.1, hz.2]
    simp
  rw [realCoefficientData_distribution basis h a] at hdist
  funext i
  exact Fintype.linearIndependent_iff.mp hind a hdist i

def scaleJetData (a : ℝ) (data : List JetDatum) : List JetDatum :=
  data.map (fun j => ((a : ℂ) * j.1, j.2.1, j.2.2))

def realBasisCombinationData {n : ℕ} (basis : Fin n → List JetDatum)
    (a : Fin n → ℝ) : List JetDatum :=
  (List.ofFn (fun i => scaleJetData (a i) (basis i))).flatten

lemma realBasisCombination_valid {n : ℕ} (basis : Fin n → List JetDatum)
    (h : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : Fin n → ℝ) :
    ∀ j ∈ realBasisCombinationData basis a, ValidJet j := by
  intro j hj
  obtain ⟨l,hl,hj⟩ := List.mem_flatten.mp hj
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hj
  exact h i z hz

lemma zeroComplex_compactRestriction (K : Set ℝ) (hK : IsCompact K) :
    zeroComplex.compactRestriction K hK = 0 := by
  ext E hE
  apply Complex.ext <;> simp [LocallyFiniteComplexMeasure.compactRestriction, zeroComplex, zeroJordan,
    localSignedCompactRestriction, SignedMeasure.toComplexMeasure_apply]

lemma actualZeroJetSum_append_compactRestriction (data rest : List JetDatum)
    (K : Set ℝ) (hK : IsCompact K) :
    (actualZeroJetSum (data ++ rest)).compactRestriction K hK =
      (actualZeroJetSum data).compactRestriction K hK +
        (actualZeroJetSum rest).compactRestriction K hK := by
  induction data with
  | nil => simp [actualZeroJetSum, zeroComplex_compactRestriction]
  | cons j data ih =>
    simp only [List.cons_append, actualZeroJetSum,
      LocallyFiniteComplexMeasure.compactRestriction_add]
    rw [ih, add_assoc]

lemma actualZeroJetSum_scale_compactRestriction (a : ℝ) (data : List JetDatum)
    (K : Set ℝ) (hK : IsCompact K) :
    (actualZeroJetSum (scaleJetData a data)).compactRestriction K hK =
      (a : ℂ) • (actualZeroJetSum data).compactRestriction K hK := by
  induction data with
  | nil =>
    rw [scaleJetData, List.map_nil, actualZeroJetSum, zeroComplex_compactRestriction]
    ext E hE
    change (0 : ℂ) = (a : ℂ) * 0
    simp
  | cons j data ih =>
    simp only [scaleJetData, List.map_cons, actualZeroJetSum,
      LocallyFiniteComplexMeasure.compactRestriction_add,
      LocallyFiniteComplexMeasure.compactRestriction_scale]
    rw [←scaleJetData, ih, smul_add, smul_smul]

lemma actualZeroJetSum_flatten_compactRestriction (data : List (List JetDatum))
    (K : Set ℝ) (hK : IsCompact K) :
    (actualZeroJetSum data.flatten).compactRestriction K hK =
      (data.map (fun row => (actualZeroJetSum row).compactRestriction K hK)).sum := by
  induction data with
  | nil => simp [actualZeroJetSum, zeroComplex_compactRestriction]
  | cons row data ih =>
    simp only [List.flatten_cons, actualZeroJetSum_append_compactRestriction,
      List.map_cons, List.sum_cons]
    rw [ih]

lemma realBasisCombination_complexCompactRestriction {n : ℕ}
    (basis : Fin n → List JetDatum) (a : Fin n → ℝ) (K : Set ℝ) (hK : IsCompact K) :
    (actualZeroJetSum (realBasisCombinationData basis a)).compactRestriction K hK =
      ∑ i, (a i : ℂ) • (actualZeroJetSum (basis i)).compactRestriction K hK := by
  simp only [realBasisCombinationData, actualZeroJetSum_flatten_compactRestriction,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply, actualZeroJetSum_scale_compactRestriction]

lemma re_complex_smul_real (a : ℝ) (μ : ComplexMeasure ℝ) :
    ComplexMeasure.re ((a : ℂ) • μ) = a • ComplexMeasure.re μ := by
  ext E hE
  change ((a : ℂ) * μ E).re = a * (μ E).re
  simp

lemma realBasisCombination_compactRestriction {n : ℕ}
    (basis : Fin n → List JetDatum) (a : Fin n → ℝ) (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction (zeroJetRealSpan (realBasisCombinationData basis a)) K hK =
      ∑ i, a i • localSignedCompactRestriction (zeroJetRealSpan (basis i)) K hK := by
  have hc := realBasisCombination_complexCompactRestriction basis a K hK
  have hr := congrArg ComplexMeasure.re hc
  simpa only [map_sum, re_complex_smul_real,
    LocallyFiniteComplexMeasure.compactRestriction_re, zeroJetRealSpan] using hr

lemma realBasisCombination_integral {n : ℕ} (basis : Fin n → List JetDatum)
    (h : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : Fin n → ℝ) (φ : 𝓢(ℝ, ℂ)) :
    (actualZeroJetSum (realBasisCombinationData basis a)).integral φ =
      ∑ i, (a i : ℂ) * (actualZeroJetSum (basis i)).integral φ := by
  rw [actualZeroJetSum_integral _ (realBasisCombination_valid basis h a)]
  simp only [realBasisCombinationData, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [actualZeroJetSum_integral _ (h i)]
  simp only [scaleJetData, List.map_map, Function.comp_def, mul_assoc]
  rw [List.sum_map_mul_left]

lemma zeroJetRealSpan_distribution_integral (data : List JetDatum)
    (h : ∀ j ∈ data, ValidJet j) (φ : 𝓢(ℝ, ℂ)) :
    (zeroJetRealSpan data).distributionOfLinearGrowth (zeroJetRealSpan_growth data h) φ =
      ((actualZeroJetSum data).integral φ +
        starRingEnd ℂ ((actualZeroJetSum data).integral (complexSchwartzConj φ))) / 2 := by
  change ((actualZeroJetSum data).rePart.distributionOfLinearGrowth
    ((actualZeroJetSum data).re_hasLinearGrowth (actualZeroJetSum_growth data h))) φ = _
  rw [←(actualZeroJetSum data).realify_distribution (actualZeroJetSum_growth data h) φ]
  rfl

lemma realBasisCombination_distribution {n : ℕ} (basis : Fin n → List JetDatum)
    (h : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : Fin n → ℝ) :
    (zeroJetRealSpan (realBasisCombinationData basis a)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (realBasisCombination_valid basis h a)) =
      ∑ i, a i • (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (h i)) := by
  ext φ
  rw [zeroJetRealSpan_distribution_integral _ (realBasisCombination_valid basis h a)]
  simp only [realBasisCombination_integral basis h a, map_sum, map_mul, Complex.conj_ofReal,
    sum_apply, smul_apply, Complex.real_smul]
  rw [←Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [zeroJetRealSpan_distribution_integral _ (h i)]
  ring

/-- A fixed independent real basis can consist of arbitrary finite realified
actual-jet combinations. Independence is on the actual embedded measures. -/
theorem independent_real_span_basis_coefficients_zero {n : ℕ}
    (basis : Fin n → List JetDatum) (h : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (hind : LinearIndependent ℝ (fun i => (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (h i)))) (a : Fin n → ℝ)
    (hoff : (zeroJetRealSpan (realBasisCombinationData basis a)).OffLatticeNonnegative) : a = 0 := by
  have hz := finite_zero_span_positive_only_zero _ (realBasisCombination_valid basis h a) hoff
  have hdist : (zeroJetRealSpan (realBasisCombinationData basis a)).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (realBasisCombination_valid basis h a)) = 0 := by
    ext φ
    rw [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply, hz.1, hz.2]
    simp
  rw [realBasisCombination_distribution basis h a] at hdist
  funext i
  exact Fintype.linearIndependent_iff.mp hind a hdist i

end Zeta23.OPICAFollowup.FiniteSpan

namespace Zeta23.OPICAFollowup
open Zeta23.OPICA FiniteSpan

/-- The actual canonical real Jordan carrier of a finite normalized zero-jet sum. -/
abbrev zeroJetRealSpan := FiniteSpan.zeroJetRealSpan

/-- Original R2-H2b, both clauses: every finite actual realified zero-jet
combination that is nonnegative off the integer lattice is the zero Jordan
measure, and its coordinates on any fixed independent real basis vanish. -/
theorem finite_zero_span_positive_only_zero :
    (∀ data : List JetDatum, ∀ h : ∀ j ∈ data, ValidJet j,
      (zeroJetRealSpan data).OffLatticeNonnegative →
        (zeroJetRealSpan data).positive = 0 ∧ (zeroJetRealSpan data).negative = 0) ∧
    (∀ n : ℕ, ∀ basis : Fin n → List JetDatum,
      ∀ h : ∀ i, ∀ j ∈ basis i, ValidJet j,
      LinearIndependent ℝ (fun i => (zeroJetRealSpan (basis i)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (h i))) →
      ∀ a : Fin n → ℝ,
      (zeroJetRealSpan (realBasisCombinationData basis a)).OffLatticeNonnegative → a = 0) := by
  exact ⟨FiniteSpan.finite_zero_span_positive_only_zero,
    fun _ basis h hind a hoff => independent_real_span_basis_coefficients_zero basis h hind a hoff⟩

end Zeta23.OPICAFollowup

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace Zeta23.OPICAFollowup.FixedBudgetSupport
open Zeta23.OPICA

def sincWeight : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (sincSquared x)

theorem sincWeight_measurable : Measurable sincWeight :=
  ENNReal.measurable_ofReal.comp sincSquared_continuous.measurable

theorem sinc_weight_finite (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (growth : LinearMassGrowth μ) : IsFiniteMeasure (μ.withDensity sincWeight) := by
  apply isFiniteMeasure_withDensity
  have h := (sincSquared_integrable_of_linear_growth μ growth).hasFiniteIntegral
  simpa only [HasFiniteIntegral,Real.enorm_of_nonneg (sincSquared_nonneg _),sincWeight] using h.ne

def sincWeightedJordan (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth) :
    JordanDecomposition ℝ where
  posPart := ν.positive.withDensity sincWeight
  negPart := ν.negative.withDensity sincWeight
  posPart_finite := sinc_weight_finite _ (ν.positive_hasLinearGrowth growth)
  negPart_finite := sinc_weight_finite _ (ν.negative_hasLinearGrowth growth)
  mutuallySingular := ((ν.mutuallySingular.withDensity).symm.withDensity).symm

def sincWeightedSigned (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth) :
    SignedMeasure ℝ := (sincWeightedJordan ν growth).toSignedMeasure

theorem sincWeightedSigned_jordan (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth) :
    (sincWeightedSigned ν growth).toJordanDecomposition=sincWeightedJordan ν growth :=
  JordanDecomposition.toJordanDecomposition_toSignedMeasure _

theorem sinc_weight_real_mass (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (growth : LinearMassGrowth μ) :
    (μ.withDensity sincWeight).real univ=∫ x, sincSquared x ∂μ := by
  rw [Measure.real,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall sincSquared_nonneg)
    sincSquared_continuous.aestronglyMeasurable).symm

theorem sinc_weight_real_apply (μ : Measure ℝ) (E : Set ℝ) (hE : MeasurableSet E) :
    (μ.withDensity sincWeight).real E=∫ x in E, sincSquared x ∂μ := by
  rw [Measure.real,withDensity_apply _ hE]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall sincSquared_nonneg)
    sincSquared_continuous.aestronglyMeasurable).symm

theorem sincWeightedSigned_apply (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth)
    (E : Set ℝ) (hE : MeasurableSet E) :
    sincWeightedSigned ν growth E=(∫ x in E, sincSquared x ∂ν.positive)-
      (∫ x in E, sincSquared x ∂ν.negative) := by
  letI := sinc_weight_finite ν.positive (ν.positive_hasLinearGrowth growth)
  letI := sinc_weight_finite ν.negative (ν.negative_hasLinearGrowth growth)
  change ((ν.positive.withDensity sincWeight).toSignedMeasure-
    (ν.negative.withDensity sincWeight).toSignedMeasure) E=_
  rw [_root_.sub_apply,Measure.toSignedMeasure_apply_measurable hE,
    Measure.toSignedMeasure_apply_measurable hE,sinc_weight_real_apply _ _ hE,
    sinc_weight_real_apply _ _ hE]

theorem sincWeightedSigned_add (μ ν : LocallyFiniteSignedMeasure)
    (hμ : μ.HasLinearGrowth) (hν : ν.HasLinearGrowth)
    (hadd : (localJordanAdd μ ν).HasLinearGrowth) :
    sincWeightedSigned (localJordanAdd μ ν) hadd=sincWeightedSigned μ hμ+sincWeightedSigned ν hν := by
  ext E hE
  rw [_root_.add_apply,sincWeightedSigned_apply _ _ _ hE,
    sincWeightedSigned_apply _ _ _ hE,sincWeightedSigned_apply _ _ _ hE]
  let f := E.indicator sincSquared
  have hmp := (sincSquared_integrable_of_linear_growth μ.positive (μ.positive_hasLinearGrowth hμ)).indicator hE
  have hmn := (sincSquared_integrable_of_linear_growth μ.negative (μ.negative_hasLinearGrowth hμ)).indicator hE
  have hnp := (sincSquared_integrable_of_linear_growth ν.positive (ν.positive_hasLinearGrowth hν)).indicator hE
  have hnn := (sincSquared_integrable_of_linear_growth ν.negative (ν.negative_hasLinearGrowth hν)).indicator hE
  have h := localJordanDifference_integral (μ.positive+ν.positive) (μ.negative+ν.negative)
    f (integrable_add_measure.mpr ⟨hmp,hnp⟩) (integrable_add_measure.mpr ⟨hmn,hnn⟩)
  rw [integral_add_measure hmp hnp,integral_add_measure hmn hnn] at h
  simp only [f,integral_indicator hE] at h
  change (∫ x in E,sincSquared x ∂(localJordanDifference _ _).positive)-
    (∫ x in E,sincSquared x ∂(localJordanDifference _ _).negative)=_
  rw [h]
  ring

theorem sincWeightedSigned_scale (a : ℝ) (μ : LocallyFiniteSignedMeasure)
    (hμ : μ.HasLinearGrowth) (hscale : (localJordanScale a μ).HasLinearGrowth) :
    sincWeightedSigned (localJordanScale a μ) hscale=a • sincWeightedSigned μ hμ := by
  ext E hE
  rw [VectorMeasure.smul_apply,sincWeightedSigned_apply _ _ _ hE,sincWeightedSigned_apply _ _ _ hE]
  let f := E.indicator sincSquared
  have hp := (sincSquared_integrable_of_linear_growth μ.positive (μ.positive_hasLinearGrowth hμ)).indicator hE
  have hn := (sincSquared_integrable_of_linear_growth μ.negative (μ.negative_hasLinearGrowth hμ)).indicator hE
  have hpp : Integrable f (Real.toNNReal a • μ.positive) :=
    hp.smul_measure (c := (Real.toNNReal a : ℝ≥0∞)) ENNReal.coe_ne_top
  have hpn : Integrable f (Real.toNNReal a • μ.negative) :=
    hn.smul_measure (c := (Real.toNNReal a : ℝ≥0∞)) ENNReal.coe_ne_top
  have hnp : Integrable f (Real.toNNReal (-a) • μ.positive) :=
    hp.smul_measure (c := (Real.toNNReal (-a) : ℝ≥0∞)) ENNReal.coe_ne_top
  have hnn : Integrable f (Real.toNNReal (-a) • μ.negative) :=
    hn.smul_measure (c := (Real.toNNReal (-a) : ℝ≥0∞)) ENNReal.coe_ne_top
  have h := localJordanDifference_integral _ _ f
    (integrable_add_measure.mpr ⟨hpp,hnn⟩) (integrable_add_measure.mpr ⟨hpn,hnp⟩)
  rw [integral_add_measure hpp hnn,integral_add_measure hpn hnp] at h
  simp only [f,integral_indicator hE,Measure.restrict_smul,
    integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul] at h
  change (∫ x in E,sincSquared x ∂(localJordanDifference _ _).positive)-
    (∫ x in E,sincSquared x ∂(localJordanDifference _ _).negative)=_
  rw [h]
  have ha : (Real.toNNReal a : ℝ)-(Real.toNNReal (-a) : ℝ)=a := by
    rw [Real.coe_toNNReal',Real.coe_toNNReal']
    rcases le_total 0 a with ha|ha
    · simp [max_eq_left ha,max_eq_right (neg_nonpos.mpr ha)]
    · simp [max_eq_right ha,max_eq_left (neg_nonneg.mpr ha)]
  conv_rhs => rw [←ha]
  simp only [smul_eq_mul]
  ring

theorem sinc_pairing_zero_of_gap (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth)
    (self : ν.FourierSelfdual growth) (gap : ν.HasUnitGap) :
    (∫ x, sincSquared x ∂ν.positive)=(∫ x, sincSquared x ∂ν.negative) := by
  have h := signed_sinc_triangle_pairing ν growth self
  rw [LocallyFiniteSignedMeasure.integral,LocallyFiniteSignedMeasure.integral,
    unitTriangle_integral_zero_of_gap _ gap.1,unitTriangle_integral_zero_of_gap _ gap.2,
    sub_self,sub_eq_zero] at h
  exact h

theorem weighted_variation_eq_twice_negative (ν : LocallyFiniteSignedMeasure)
    (growth : ν.HasLinearGrowth) (self : ν.FourierSelfdual growth) (gap : ν.HasUnitGap) :
    (sincWeightedSigned ν growth).totalVariation.real univ=
      2*(∫ x, sincSquared x ∂ν.negative) := by
  letI := sinc_weight_finite ν.positive (ν.positive_hasLinearGrowth growth)
  letI := sinc_weight_finite ν.negative (ν.negative_hasLinearGrowth growth)
  rw [SignedMeasure.totalVariation,sincWeightedSigned_jordan]
  change (ν.positive.withDensity sincWeight+ν.negative.withDensity sincWeight).real univ=_
  rw [measureReal_add_apply,
    sinc_weight_real_mass _ (ν.positive_hasLinearGrowth growth),
    sinc_weight_real_mass _ (ν.negative_hasLinearGrowth growth),
    sinc_pairing_zero_of_gap ν growth self gap]
  ring

theorem negative_weight_zero_iff_zero (ν : LocallyFiniteSignedMeasure)
    (growth : ν.HasLinearGrowth) (self : ν.FourierSelfdual growth) (gap : ν.HasUnitGap) :
    (∫ x, sincSquared x ∂ν.negative)=0 ↔ ν.positive=0 ∧ ν.negative=0 := by
  constructor
  · intro h
    exact signed_sharp_gap_separator ν growth self gap
      (lattice_support_of_sincSquared_integral_zero _ (ν.negative_hasLinearGrowth growth) h)
  · rintro ⟨_,hneg⟩
    simp [hneg]

theorem sincWeightedSigned_zero_iff_zero (ν : LocallyFiniteSignedMeasure)
    (growth : ν.HasLinearGrowth) (self : ν.FourierSelfdual growth) (gap : ν.HasUnitGap) :
    sincWeightedSigned ν growth=0 ↔ ν.positive=0 ∧ ν.negative=0 := by
  constructor
  · intro hz
    have h := weighted_variation_eq_twice_negative ν growth self gap
    rw [hz,SignedMeasure.totalVariation_zero] at h
    simp only [Measure.real,Measure.coe_zero,Pi.zero_apply,ENNReal.toReal_zero] at h
    exact (negative_weight_zero_iff_zero ν growth self gap).mp (by linarith)
  · rintro ⟨hp,hn⟩
    ext E hE
    rw [sincWeightedSigned_apply _ _ _ hE,hp,hn]
    simp

theorem negative_sinc_off_lattice_eq_global (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] (growth : LinearMassGrowth μ) (origin : μ {0}=0) :
    (∫ x in integerLatticeᶜ,sincSquared x ∂μ)=∫ x,sincSquared x ∂μ := by
  have hLat : (μ.restrict integerLattice) integerLatticeᶜ=0 := by
    rw [Measure.restrict_apply integerLattice_measurable.compl]
    simp
  have hOrigin : (μ.restrict integerLattice) {0}=0 :=
    le_antisymm ((Measure.restrict_le_self {0}).trans (le_of_eq origin)) zero_le
  have hz := sincSquared_integral_zero_of_lattice_support
    (μ.restrict integerLattice) hLat hOrigin
  have h := integral_add_compl integerLattice_measurable
    (sincSquared_integrable_of_linear_growth μ growth)
  rw [hz,zero_add] at h
  exact h

end Zeta23.OPICAFollowup.FixedBudgetSupport

noncomputable section
open Set Metric
namespace Zeta23.OPICAFollowup.FixedBasisSupport

/-- Compactness supplies a constant for one fixed finite-dimensional space.
This generic supporting lemma asserts no uniformity over changing bases. -/
theorem fixed_space_positive_homogeneous_budget
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (continuous_f : Continuous f)
    (positive : ∀ x : E, x ≠ 0 → 0 < f x)
    (homogeneous : ∀ (a : ℝ), 0 ≤ a → ∀ x : E, f (a • x) = a * f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, c * ‖x‖ ≤ f x := by
  have f_zero : f 0 = 0 := by simpa using homogeneous 0 le_rfl (0 : E)
  rcases subsingleton_or_nontrivial E with hs | hn
  · letI := hs
    refine ⟨1, zero_lt_one, fun x => ?_⟩
    rw [Subsingleton.elim x 0, norm_zero, mul_zero, f_zero]
  · letI := hn
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have nv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have unit_norm {x : E} (hx : x ≠ 0) : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
    have nonempty_sphere : (sphere (0 : E) 1).Nonempty :=
      ⟨(‖v‖⁻¹ : ℝ) • v, by simpa only [mem_sphere, dist_zero_right] using unit_norm hv⟩
    obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      nonempty_sphere continuous_f.continuousOn
    have nu : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
    have une : u ≠ 0 := fun h => by simpa [h] using nu
    refine ⟨f u, positive u une, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx, f_zero]
    · have hunit : (‖x‖⁻¹ : ℝ) • x ∈ sphere (0 : E) 1 := by
        simpa only [mem_sphere, dist_zero_right] using unit_norm hx
      have h := mul_le_mul_of_nonneg_right (hmin hunit) (norm_nonneg x)
      rw [homogeneous _ (inv_nonneg.mpr (norm_nonneg x)) x] at h
      simpa only [mul_assoc, mul_comm ‖x‖⁻¹ (f x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), mul_one] using h

end Zeta23.OPICAFollowup.FixedBasisSupport

noncomputable section
open Set MeasureTheory
namespace Zeta23.OPICAFollowup.FixedBasisSupport

local instance : Norm (SignedMeasure ℝ) := ⟨fun μ => μ.totalVariation.real univ⟩

theorem signed_variation_norm_core : NormedSpace.Core ℝ (SignedMeasure ℝ) where
  norm_nonneg μ := ENNReal.toReal_nonneg
  norm_smul a μ := by
    change (a • μ).totalVariation.real univ = ‖a‖ * μ.totalVariation.real univ
    simp only [SignedMeasure.totalVariation_eq_variation,VectorMeasure.variation_smul,
      Measure.real,Measure.smul_apply,Measure.nnreal_smul_coe_apply,
      ENNReal.toReal_mul,ENNReal.coe_toReal,coe_nnnorm]
  norm_triangle μ ν := by
    change (μ+ν).totalVariation.real univ ≤ μ.totalVariation.real univ+ν.totalVariation.real univ
    have h := VectorMeasure.variation_add_le (μ := μ) (ν := ν) univ
    rw [←SignedMeasure.totalVariation_eq_variation,
      ←SignedMeasure.totalVariation_eq_variation,
      ←SignedMeasure.totalVariation_eq_variation,Measure.add_apply] at h
    exact (ENNReal.toReal_mono (by finiteness) h).trans_eq
      (ENNReal.toReal_add (by finiteness) (by finiteness))
  norm_eq_zero_iff μ := by
    change μ.totalVariation.real univ=0 ↔ μ=0
    constructor
    · intro h
      have hz : μ.totalVariation univ=0 :=
        (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (by finiteness)
      exact VectorMeasure.variation_eq_zero.mp
        (SignedMeasure.totalVariation_eq_variation μ ▸ (Measure.measure_univ_eq_zero.mp hz))
    · intro h
      simp [h,SignedMeasure.totalVariation_zero,Measure.real]

local instance : NormedAddCommGroup (SignedMeasure ℝ) :=
  NormedAddCommGroup.ofCore signed_variation_norm_core
local instance : NormedSpace ℝ (SignedMeasure ℝ) :=
  NormedSpace.ofCore signed_variation_norm_core

/-- Every fixed injective finite-dimensional map into actual finite signed
measures has a strictly positive total-variation lower bound. The normed
signed-measure structure is local to this supporting proof. -/
theorem fixed_linear_signed_variation_budget
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] SignedMeasure ℝ) (injective : Function.Injective L) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, c*‖x‖ ≤ (L x).totalVariation.real univ := by
  apply fixed_space_positive_homogeneous_budget (fun x => ‖L x‖)
  · exact L.continuous_of_finiteDimensional.norm
  · intro x hx
    exact norm_pos_iff.mpr (fun h => hx (injective (by simpa using h)))
  · intro a ha x
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]

end Zeta23.OPICAFollowup.FixedBasisSupport

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform ENNReal NNReal

namespace Zeta23.OPICAFollowup.FiniteSpan
open Zeta23.OPICA FixedBudgetSupport

lemma signed_zero_growth : zeroJordan.HasLinearGrowth := by
  refine ⟨0, le_rfl, fun R hR => ?_⟩
  simp [zeroJordan, LocallyFiniteSignedMeasure.totalVariation, Measure.real]

lemma signed_as_complex_growth (μ : LocallyFiniteSignedMeasure) (h : μ.HasLinearGrowth) :
    (⟨μ, zeroJordan⟩ : LocallyFiniteComplexMeasure).HasLinearGrowth := by
  simpa only [LocallyFiniteComplexMeasure.HasLinearGrowth,
    LocallyFiniteComplexMeasure.variationControl, zeroJordan,
    LocallyFiniteSignedMeasure.HasLinearGrowth,
    LocallyFiniteSignedMeasure.totalVariation, add_zero] using h

lemma signed_add_growth (μ ν : LocallyFiniteSignedMeasure)
    (hμ : μ.HasLinearGrowth) (hν : ν.HasLinearGrowth) : (localJordanAdd μ ν).HasLinearGrowth := by
  exact LocallyFiniteComplexMeasure.re_hasLinearGrowth
    ((⟨μ, zeroJordan⟩ : LocallyFiniteComplexMeasure).add ⟨ν,zeroJordan⟩)
    (LocallyFiniteComplexMeasure.hasLinearGrowth_add _ _
      (signed_as_complex_growth μ hμ) (signed_as_complex_growth ν hν))

lemma signed_scale_growth (a : ℝ) (μ : LocallyFiniteSignedMeasure)
    (hμ : μ.HasLinearGrowth) : (localJordanScale a μ).HasLinearGrowth := by
  obtain ⟨A,hA,hAb⟩ := hμ
  refine ⟨|a| * A,mul_nonneg (abs_nonneg _) hA,fun R hR => ?_⟩
  have hle := localJordanScale_totalVariation_le a μ (Icc (-R) R)
  rw [Measure.smul_apply,smul_eq_mul] at hle
  have hfin : ENNReal.ofReal |a| * μ.totalVariation (Icc (-R) R)≠∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top isCompact_Icc.measure_lt_top.ne
  have hh := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] at hh
  have ha := hAb R hR
  change (μ.totalVariation (Icc (-R) R)).toReal≤_ at ha
  change ((localJordanScale a μ).totalVariation (Icc (-R) R)).toReal≤_
  calc
    _ ≤ |a| * (μ.totalVariation (Icc (-R) R)).toReal := hh
    _ ≤ |a| * (A * (1+R)) := mul_le_mul_of_nonneg_left ha (abs_nonneg a)
    _ = _ := by ring

/-- Generic finite Jordan algebra with growth already proved for each input.
The actual basis below supplies these proofs from the actual zero jets. -/
abbrev GrowingSignedDatum := ℝ × {μ : LocallyFiniteSignedMeasure // μ.HasLinearGrowth}

def signedListSum : List GrowingSignedDatum → LocallyFiniteSignedMeasure
  | [] => zeroJordan
  | j :: rest => localJordanAdd (localJordanScale j.1 j.2.1) (signedListSum rest)

lemma signedListSum_growth (data : List GrowingSignedDatum) : (signedListSum data).HasLinearGrowth := by
  induction data with
  | nil => exact signed_zero_growth
  | cons j rest ih => exact signed_add_growth _ _ (signed_scale_growth _ _ j.2.2) ih

lemma zeroJordan_compactRestriction (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction zeroJordan K hK = 0 := by
  ext E hE
  simp [zeroJordan, localSignedCompactRestriction]

lemma signedListSum_compactRestriction (data : List GrowingSignedDatum)
    (K : Set ℝ) (hK : IsCompact K) :
    localSignedCompactRestriction (signedListSum data) K hK =
      (data.map (fun j => j.1 • localSignedCompactRestriction j.2.1 K hK)).sum := by
  induction data with
  | nil => simp [signedListSum, zeroJordan_compactRestriction]
  | cons j rest ih =>
    rw [signedListSum, localJordanAdd_compactRestriction, localJordanScale_compactRestriction, ih]
    rfl

lemma zeroJordan_weighted : sincWeightedSigned zeroJordan signed_zero_growth = 0 := by
  ext E hE
  rw [sincWeightedSigned_apply _ _ _ hE]
  simp [zeroJordan]

lemma signedListSum_weighted (data : List GrowingSignedDatum) :
    sincWeightedSigned (signedListSum data) (signedListSum_growth data) =
      (data.map (fun j => j.1 • sincWeightedSigned j.2.1 j.2.2)).sum := by
  induction data with
  | nil => simp [signedListSum, zeroJordan_weighted]
  | cons j rest ih =>
    change sincWeightedSigned (localJordanAdd (localJordanScale j.1 j.2.1) (signedListSum rest))
      (signed_add_growth _ _ (signed_scale_growth _ _ j.2.2) (signedListSum_growth rest)) = _
    rw [sincWeightedSigned_add _ _ (signed_scale_growth _ _ j.2.2)
      (signedListSum_growth rest), sincWeightedSigned_scale, ih]
    rfl

lemma signed_eq_of_compactRestrictions (μ ν : LocallyFiniteSignedMeasure)
    (h : ∀ K : Set ℝ, ∀ hK : IsCompact K,
      localSignedCompactRestriction μ K hK = localSignedCompactRestriction ν K hK) : μ = ν := by
  have hpK (K : Set ℝ) (hK : IsCompact K) : μ.positive.restrict K = ν.positive.restrict K := by
    have hp := congrArg (fun s : SignedMeasure ℝ => s.toJordanDecomposition.posPart) (h K hK)
    simpa only [localSignedCompactRestriction_jordan, localSignedCompactJordan] using hp
  have hnK (K : Set ℝ) (hK : IsCompact K) : μ.negative.restrict K = ν.negative.restrict K := by
    have hn := congrArg (fun s : SignedMeasure ℝ => s.toJordanDecomposition.negPart) (h K hK)
    simpa only [localSignedCompactRestriction_jordan, localSignedCompactJordan] using hn
  have hp : μ.positive = ν.positive :=
    Measure.ext_of_iUnion_eq_univ localMeasureInterval_cover (fun n => hpK _ isCompact_Icc)
  have hn : μ.negative = ν.negative :=
    Measure.ext_of_iUnion_eq_univ localMeasureInterval_cover (fun n => hnK _ isCompact_Icc)
  cases μ
  cases ν
  cases hp
  cases hn
  rfl

def basisSignedData {n : ℕ} (basis : Fin n → List JetDatum)
    (h : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : Fin n → ℝ) : List GrowingSignedDatum :=
  List.ofFn (fun i => (a i, ⟨zeroJetRealSpan (basis i), zeroJetRealSpan_growth _ (h i)⟩))

lemma realBasisCombination_eq_signedListSum {n : ℕ} (basis : Fin n → List JetDatum)
    (h : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : Fin n → ℝ) :
    zeroJetRealSpan (realBasisCombinationData basis a) = signedListSum (basisSignedData basis h a) := by
  apply signed_eq_of_compactRestrictions
  intro K hK
  rw [realBasisCombination_compactRestriction, signedListSum_compactRestriction]
  simp only [basisSignedData, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

lemma sincWeightedSigned_congr (μ ν : LocallyFiniteSignedMeasure)
    (hμ : μ.HasLinearGrowth) (hν : ν.HasLinearGrowth) (heq : μ = ν) :
    sincWeightedSigned μ hμ = sincWeightedSigned ν hν := by
  cases heq
  rfl

theorem realBasisCombination_weightedSigned {n : ℕ} (basis : Fin n → List JetDatum)
    (h : ∀ i, ∀ j ∈ basis i, ValidJet j) (a : Fin n → ℝ) :
    sincWeightedSigned (zeroJetRealSpan (realBasisCombinationData basis a))
        (zeroJetRealSpan_growth _ (realBasisCombination_valid basis h a)) =
      ∑ i, a i • sincWeightedSigned (zeroJetRealSpan (basis i)) (zeroJetRealSpan_growth _ (h i)) := by
  have heq := realBasisCombination_eq_signedListSum basis h a
  have hw := sincWeightedSigned_congr _ _
    (zeroJetRealSpan_growth _ (realBasisCombination_valid basis h a))
    (signedListSum_growth (basisSignedData basis h a)) heq
  rw [hw, signedListSum_weighted]
  simp only [basisSignedData, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

end Zeta23.OPICAFollowup.FiniteSpan

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Zeta23.OPICAFollowup
open Zeta23.OPICA FiniteSpan FixedBudgetSupport

/-- The map contains the literal sinc-weighted signed measures of each
fixed actual realified zero-jet basis vector. -/
def actualFixedBasisWeightedMap {n : ℕ} (basis : Fin n → List JetDatum)
    (valid : ∀ i, ∀ j ∈ basis i, ValidJet j) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] SignedMeasure ℝ where
  toFun a := ∑ i, a i • sincWeightedSigned (zeroJetRealSpan (basis i))
    (zeroJetRealSpan_growth _ (valid i))
  map_add' a b := by
    simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [PiLp.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]

theorem actualFixedBasisWeightedMap_eq_combination {n : ℕ}
    (basis : Fin n → List JetDatum) (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (a : EuclideanSpace ℝ (Fin n)) :
    actualFixedBasisWeightedMap basis valid a=
      sincWeightedSigned (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i)))
        (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid _)) :=
  (realBasisCombination_weightedSigned basis valid (fun i => a i)).symm

theorem actualFixedBasisWeightedMap_injective {n : ℕ}
    (basis : Fin n → List JetDatum) (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (independent : LinearIndependent ℝ (fun i =>
      (zeroJetRealSpan (basis i)).distributionOfLinearGrowth (zeroJetRealSpan_growth _ (valid i)))) :
    Function.Injective (actualFixedBasisWeightedMap basis valid) := by
  intro a b hab
  apply sub_eq_zero.mp
  have hw : actualFixedBasisWeightedMap basis valid (a-b)=0 := by
    rw [map_sub,hab,sub_self]
  rw [actualFixedBasisWeightedMap_eq_combination] at hw
  let data := realBasisCombinationData basis (fun i => (a-b) i)
  have hv := realBasisCombination_valid basis valid (fun i => (a-b) i)
  have hz := (sincWeightedSigned_zero_iff_zero (zeroJetRealSpan data)
    (zeroJetRealSpan_growth data hv) (zeroJetRealSpan_selfdual data hv)
    (zeroJetRealSpan_gap data)).mp hw
  have hoff : (zeroJetRealSpan data).OffLatticeNonnegative := by
    rw [LocallyFiniteSignedMeasure.OffLatticeNonnegative,hz.2]
    simp
  have ha := Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero.2 n basis valid independent
    (fun i => (a-b) i) hoff
  exact PiLp.ext fun i => congrFun ha i

/-- Original fixed-independent-real-basis budget. Every basis vector is a
finite genuine zero-jet combination; the actual Jordan negative measure is
globally sinc weighted off the integer lattice. The coefficient norm is the
Euclidean norm. No constant is asserted uniformly over different bases. -/
theorem fixed_basis_negative_mass_budget {n : ℕ}
    (basis : Fin n → List JetDatum) (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (independent : LinearIndependent ℝ (fun i =>
      (zeroJetRealSpan (basis i)).distributionOfLinearGrowth (zeroJetRealSpan_growth _ (valid i)))) :
    ∃ c_basis : ℝ, 0<c_basis ∧ ∀ a : EuclideanSpace ℝ (Fin n),
      c_basis*‖a‖ ≤ ∫ x in integerLatticeᶜ, sincSquared x
        ∂(zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).negative := by
  obtain ⟨c,hc,hbound⟩ := Zeta23.OPICAFollowup.FixedBasisSupport.fixed_linear_signed_variation_budget
    (actualFixedBasisWeightedMap basis valid) (actualFixedBasisWeightedMap_injective basis valid independent)
  refine ⟨c/2,by positivity,fun a => ?_⟩
  have h := hbound a
  rw [actualFixedBasisWeightedMap_eq_combination] at h
  let data := realBasisCombinationData basis (fun i => a i)
  have hv := realBasisCombination_valid basis valid (fun i => a i)
  rw [weighted_variation_eq_twice_negative (zeroJetRealSpan data)
    (zeroJetRealSpan_growth data hv) (zeroJetRealSpan_selfdual data hv)
    (zeroJetRealSpan_gap data)] at h
  have hoff := negative_sinc_off_lattice_eq_global (zeroJetRealSpan data).negative
    ((zeroJetRealSpan data).negative_hasLinearGrowth (zeroJetRealSpan_growth data hv))
    (singleton_zero_of_unit_gap _ (zeroJetRealSpan_gap data).2)
  change c/2*‖a‖ ≤ ∫ x in integerLatticeᶜ,sincSquared x ∂(zeroJetRealSpan data).negative
  rw [hoff]
  linarith

/-- The exact signed sinc balance makes negative mass even on the actual
finite coefficient space; no independence premise is needed for this identity. -/
theorem actual_basis_negative_mass_even {n : ℕ}
    (basis : Fin n → List JetDatum) (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (a : EuclideanSpace ℝ (Fin n)) :
    (∫ x,sincSquared x ∂(zeroJetRealSpan
      (realBasisCombinationData basis (fun i => (-a) i))).negative)=
    (∫ x,sincSquared x ∂(zeroJetRealSpan
      (realBasisCombinationData basis (fun i => a i))).negative) := by
  have hpos := weighted_variation_eq_twice_negative
    (zeroJetRealSpan (realBasisCombinationData basis (fun i => a i)))
    (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid _))
    (zeroJetRealSpan_selfdual _ (realBasisCombination_valid basis valid _))
    (zeroJetRealSpan_gap _)
  have hneg := weighted_variation_eq_twice_negative
    (zeroJetRealSpan (realBasisCombinationData basis (fun i => (-a) i)))
    (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid _))
    (zeroJetRealSpan_selfdual _ (realBasisCombination_valid basis valid _))
    (zeroJetRealSpan_gap _)
  rw [←actualFixedBasisWeightedMap_eq_combination basis valid a] at hpos
  rw [←actualFixedBasisWeightedMap_eq_combination basis valid (-a)] at hneg
  rw [map_neg,SignedMeasure.totalVariation_neg] at hneg
  linarith

end Zeta23.OPICAFollowup

#print axioms Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero
#print axioms Zeta23.OPICAFollowup.fixed_basis_negative_mass_budget
#print axioms Zeta23.OPICAFollowup.actual_basis_negative_mass_even
#print axioms Zeta23.OPICAFollowup.FiniteSpan.signed_eq_of_compactRestrictions
