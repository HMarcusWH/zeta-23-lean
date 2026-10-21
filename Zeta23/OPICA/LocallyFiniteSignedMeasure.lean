import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Locally finite Jordan pairs

A pair of mutually singular, locally finite positive measures represents a
locally finite real signed measure without evaluating `infinity - infinity`.
No finiteness of either measure on the whole line is imposed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped SchwartzMap ContDiff CompactlySupported Convolution Topology Pointwise

namespace Zeta23.OPICA

structure LocallyFiniteSignedMeasure where
  positive : Measure ℝ
  negative : Measure ℝ
  positive_locallyFinite : IsLocallyFiniteMeasure positive
  negative_locallyFinite : IsLocallyFiniteMeasure negative
  mutuallySingular : positive.MutuallySingular negative

attribute [instance] LocallyFiniteSignedMeasure.positive_locallyFinite
  LocallyFiniteSignedMeasure.negative_locallyFinite

/-- Linear growth is tested on bounded symmetric intervals only. -/
def LinearMassGrowth (μ : Measure ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → μ.real (Icc (-R) R) ≤ C * (1 + R)

def LocallyFiniteSignedMeasure.totalVariation (ν : LocallyFiniteSignedMeasure) : Measure ℝ :=
  ν.positive + ν.negative

instance LocallyFiniteSignedMeasure.totalVariation_locallyFinite (ν : LocallyFiniteSignedMeasure) :
    IsLocallyFiniteMeasure ν.totalVariation where
  finiteAtNhds x := by
    obtain ⟨s, hs, hsfinite⟩ := ν.positive.finiteAt_nhds x
    obtain ⟨t, ht, htfinite⟩ := ν.negative.finiteAt_nhds x
    refine ⟨s ∩ t, Filter.inter_mem hs ht, ?_⟩
    rw [LocallyFiniteSignedMeasure.totalVariation, Measure.add_apply]
    exact ENNReal.add_lt_top.mpr
      ⟨(measure_mono inter_subset_left).trans_lt hsfinite,
        (measure_mono inter_subset_right).trans_lt htfinite⟩

def LocallyFiniteSignedMeasure.HasLinearGrowth (ν : LocallyFiniteSignedMeasure) : Prop :=
  LinearMassGrowth ν.totalVariation

theorem LinearMassGrowth.mono {μ η : Measure ℝ} [IsLocallyFiniteMeasure η]
    (hη : LinearMassGrowth η) (hle : μ ≤ η) : LinearMassGrowth μ := by
  obtain ⟨C, hC, hbound⟩ := hη
  refine ⟨C, hC, fun R hR => ?_⟩
  exact (ENNReal.toReal_mono isCompact_Icc.measure_lt_top.ne (hle (Icc (-R) R))).trans
    (hbound R hR)

theorem LocallyFiniteSignedMeasure.positive_hasLinearGrowth (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) : LinearMassGrowth ν.positive := by
  apply hν.mono
  intro s
  rw [LocallyFiniteSignedMeasure.totalVariation, Measure.add_apply]
  exact le_add_of_nonneg_right (by positivity)

theorem LocallyFiniteSignedMeasure.negative_hasLinearGrowth (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) : LinearMassGrowth ν.negative := by
  apply hν.mono
  intro s
  rw [LocallyFiniteSignedMeasure.totalVariation, Measure.add_apply]
  exact le_add_of_nonneg_left (by positivity)

/-- Signed integration is the difference of two ordinary integrals. Its use
requires integrability against the sum of the Jordan measures. -/
def LocallyFiniteSignedMeasure.integral (ν : LocallyFiniteSignedMeasure) (f : ℝ → ℝ) : ℝ :=
  (∫ x, f x ∂ν.positive) - ∫ x, f x ∂ν.negative

/-- The signed distribution associated to a Jordan pair whose two measures
have temperate growth. This construction by itself makes no faithfulness or
linear-growth implication claim. -/
def LocallyFiniteSignedMeasure.toTemperedDistribution (ν : LocallyFiniteSignedMeasure)
    [ν.positive.HasTemperateGrowth] [ν.negative.HasTemperateGrowth] :
    TemperedDistribution ℝ ℂ :=
  ν.positive.toTemperedDistribution - ν.negative.toTemperedDistribution

theorem LocallyFiniteSignedMeasure.toTemperedDistribution_apply
    (ν : LocallyFiniteSignedMeasure)
    [ν.positive.HasTemperateGrowth] [ν.negative.HasTemperateGrowth]
    (f : SchwartzMap ℝ ℂ) :
    ν.toTemperedDistribution f = (∫ x, f x ∂ν.positive) - ∫ x, f x ∂ν.negative := by
  rfl

/-- An integrable test against the variation is integrable against each
Jordan part; global finite variation is not required. -/
theorem LocallyFiniteSignedMeasure.integrable_parts (ν : LocallyFiniteSignedMeasure)
    {f : ℝ → ℝ} (hf : Integrable f ν.totalVariation) :
    Integrable f ν.positive ∧ Integrable f ν.negative := by
  exact integrable_add_measure.mp hf

private def dyadicShell (n : ℕ) : Set ℝ :=
  Icc (-((2 : ℝ) ^ (n + 1))) ((2 : ℝ) ^ (n + 1)) \
    Ioo (-((2 : ℝ) ^ n)) ((2 : ℝ) ^ n)

private theorem dyadicShell_compact (n : ℕ) : IsCompact (dyadicShell n) :=
  isCompact_Icc.diff isOpen_Ioo

def quadraticDecay (x : ℝ) : ℝ := 1 / (1 + |x|) ^ 2

theorem quadraticDecay_nonneg (x : ℝ) : 0 ≤ quadraticDecay x := by
  unfold quadraticDecay
  positivity

theorem quadraticDecay_continuous : Continuous quadraticDecay := by
  unfold quadraticDecay
  exact continuous_const.div ((continuous_const.add continuous_abs).pow 2)
    (fun x => pow_ne_zero _ (by positivity))

/-- Linear mass growth suffices for the quadratic decay used in the signed
separator. The proof uses genuine dyadic shells and a geometric majorant. -/
theorem quadraticDecay_integrable_of_linear_growth (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] (hμ : LinearMassGrowth μ) : Integrable quadraticDecay μ := by
  obtain ⟨C, hC, hbound⟩ := hμ
  have hshell (n : ℕ) : IntegrableOn quadraticDecay (dyadicShell n) μ :=
    quadraticDecay_continuous.continuousOn.integrableOn_compact (dyadicShell_compact n)
  have hsum : Summable (fun n : ℕ => ∫ x in dyadicShell n, ‖quadraticDecay x‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (f := fun n : ℕ => (3 * C) * (1 / 2 : ℝ) ^ n)
    · intro n
      have ha : 0 < (2 : ℝ) ^ n := by positivity
      have haone : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hpoint (x : ℝ) (hx : x ∈ dyadicShell n) :
          ‖quadraticDecay x‖ ≤ 1 / ((2 : ℝ) ^ n) ^ 2 := by
        have hlow : (2 : ℝ) ^ n ≤ |x| := by
          by_contra h
          have hlt : |x| < (2 : ℝ) ^ n := lt_of_not_ge h
          exact hx.2 (abs_lt.mp hlt)
        rw [Real.norm_eq_abs, abs_of_nonneg (quadraticDecay_nonneg x)]
        unfold quadraticDecay
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [abs_nonneg x]
      have hmeasure : μ.real (dyadicShell n) ≤ 3 * C * (2 : ℝ) ^ n := by
        calc
          _ ≤ μ.real (Icc (-((2 : ℝ) ^ (n + 1))) ((2 : ℝ) ^ (n + 1))) :=
            measureReal_mono (fun x hx => hx.1) isCompact_Icc.measure_lt_top.ne
          _ ≤ C * (1 + (2 : ℝ) ^ (n + 1)) := hbound _ (by positivity)
          _ ≤ 3 * C * (2 : ℝ) ^ n := by
            rw [pow_succ]
            nlinarith
      calc
        _ = ‖∫ x in dyadicShell n, quadraticDecay x ∂μ‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg quadraticDecay_nonneg)]
          congr 1
          funext x
          exact Real.norm_of_nonneg (quadraticDecay_nonneg x)
        _ ≤ (1 / ((2 : ℝ) ^ n) ^ 2) * μ.real (dyadicShell n) :=
          norm_setIntegral_le_of_norm_le_const (dyadicShell_compact n).measure_lt_top hpoint
        _ ≤ (1 / ((2 : ℝ) ^ n) ^ 2) * (3 * C * (2 : ℝ) ^ n) := by
          exact mul_le_mul_of_nonneg_left hmeasure (by positivity)
        _ = (3 * C) * (1 / 2 : ℝ) ^ n := by
          rw [div_pow, one_pow]
          field_simp
    · exact (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left _
  have hshells : IntegrableOn quadraticDecay (⋃ n, dyadicShell n) μ :=
    integrableOn_iUnion_of_summable_integral_norm hshell hsum
  have hcore : IntegrableOn quadraticDecay (Icc (-1) 1) μ :=
    quadraticDecay_continuous.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Icc (-1 : ℝ) 1 ∪ (⋃ n, dyadicShell n) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : |x| ≤ 1
    · exact Or.inl (abs_le.mp hx)
    · obtain ⟨n, hn, hnnext⟩ := exists_nat_pow_near (le_of_not_ge hx) (by norm_num : (1 : ℝ) < 2)
      refine Or.inr (mem_iUnion.mpr ⟨n, ?_⟩)
      refine ⟨abs_le.mp hnnext.le, ?_⟩
      intro hsmall
      exact (not_lt_of_ge hn) (abs_lt.mpr hsmall)
  have := hcore.union hshells
  rwa [hcover, integrableOn_univ] at this

/-- The distributional embedding therefore applies to every locally finite
positive measure with the stated linear growth; temperateness is derived
from the growth bound. -/
theorem hasTemperateGrowth_of_linear_growth (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] (hμ : LinearMassGrowth μ) : μ.HasTemperateGrowth := by
  refine ⟨⟨2, ?_⟩⟩
  have heq : (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) = quadraticDecay := by
    funext x
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [quadraticDecay, one_div]
  change Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) μ
  rw [heq]
  exact quadraticDecay_integrable_of_linear_growth μ hμ

theorem LocallyFiniteSignedMeasure.quadraticDecay_integrable
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) :
    Integrable quadraticDecay ν.totalVariation := by
  exact quadraticDecay_integrable_of_linear_growth ν.totalVariation hν

theorem LocallyFiniteSignedMeasure.parts_temperate_of_linear_growth
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) :
    ν.positive.HasTemperateGrowth ∧ ν.negative.HasTemperateGrowth := by
  have hparts := ν.integrable_parts (ν.quadraticDecay_integrable hν)
  have heq : (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) = quadraticDecay := by
    funext x
    rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [quadraticDecay, one_div]
  constructor
  · refine ⟨⟨2, ?_⟩⟩
    change Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) ν.positive
    rw [heq]
    exact hparts.1
  · refine ⟨⟨2, ?_⟩⟩
    change Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) ν.negative
    rw [heq]
    exact hparts.2

/-- The actual distribution associated to a linearly growing Jordan pair,
with temperateness supplied by the proved dyadic estimate. -/
def LocallyFiniteSignedMeasure.distributionOfLinearGrowth
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) : TemperedDistribution ℝ ℂ :=
  letI := (ν.parts_temperate_of_linear_growth hν).1
  letI := (ν.parts_temperate_of_linear_growth hν).2
  ν.toTemperedDistribution

theorem LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) (f : SchwartzMap ℝ ℂ) :
    ν.distributionOfLinearGrowth hν f =
      (∫ x, f x ∂ν.positive) - ∫ x, f x ∂ν.negative := by
  rfl

/-- A linearly growing Jordan pair whose actual distribution vanishes has
both Jordan parts zero. The proof tests the bounded sign density with
compactly supported smooth functions; no faithfulness premise is assumed. -/
theorem LocallyFiniteSignedMeasure.parts_eq_zero_of_distribution_eq_zero
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth)
    (hzero : ν.distributionOfLinearGrowth hν = 0) :
    ν.positive = 0 ∧ ν.negative = 0 := by
  classical
  obtain ⟨s, hs, hspos, hsneg⟩ := ν.mutuallySingular
  let signDensity : ℝ → ℝ := s.piecewise (fun _ => -1) (fun _ => 1)
  have hsignmeas : Measurable signDensity :=
    measurable_const.piecewise hs measurable_const
  have hsignnorm (x : ℝ) : ‖signDensity x‖ = 1 := by
    by_cases hx : x ∈ s <;> simp [signDensity, hx]
  have hsignloc : LocallyIntegrable signDensity ν.totalVariation := by
    apply (locallyIntegrable_const (1 : ℝ)).mono hsignmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by rw [hsignnorm]; norm_num)
  have hposae : ∀ᵐ x ∂ν.positive, x ∉ s := by
    apply ae_iff.mpr
    simpa using hspos
  have hnegae : ∀ᵐ x ∂ν.negative, x ∈ s := by
    apply ae_iff.mpr
    exact hsneg
  have hsignzero : ∀ᵐ x ∂ν.totalVariation, signDensity x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hsignloc
    intro g hg hgcompact
    have hgpos : Integrable g ν.positive := hg.continuous.integrable_of_hasCompactSupport hgcompact
    have hgneg : Integrable g ν.negative := hg.continuous.integrable_of_hasCompactSupport hgcompact
    have hintpos : Integrable (fun x => g x * signDensity x) ν.positive := by
      apply hgpos.mono (hg.continuous.aestronglyMeasurable.mul hsignmeas.aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun x => by rw [Pi.mul_apply, norm_mul, hsignnorm, mul_one])
    have hintneg : Integrable (fun x => g x * signDensity x) ν.negative := by
      apply hgneg.mono (hg.continuous.aestronglyMeasurable.mul hsignmeas.aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun x => by rw [Pi.mul_apply, norm_mul, hsignnorm, mul_one])
    have hposint : (∫ x, g x * signDensity x ∂ν.positive) = ∫ x, g x ∂ν.positive := by
      apply integral_congr_ae
      filter_upwards [hposae] with x hx
      simp [signDensity, hx]
    have hnegint : (∫ x, g x * signDensity x ∂ν.negative) = -(∫ x, g x ∂ν.negative) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hnegae] with x hx
      simp [signDensity, hx]
    have hcpt : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgcompact.comp_left rfl
    have hsmooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    let test : SchwartzMap ℝ ℂ := hcpt.toSchwartzMap hsmooth
    have hd := congrArg (fun T : TemperedDistribution ℝ ℂ => T test) hzero
    rw [ν.distributionOfLinearGrowth_apply hν test] at hd
    have hreal : (∫ x, g x ∂ν.positive) - ∫ x, g x ∂ν.negative = 0 := by
      apply Complex.ofReal_injective
      have hd' : (∫ x, (g x : ℂ) ∂ν.positive) - ∫ x, (g x : ℂ) ∂ν.negative = 0 := by
        simpa [test, Function.comp_def] using hd
      rw [integral_complex_ofReal, integral_complex_ofReal] at hd'
      simpa only [Complex.ofReal_sub, Complex.ofReal_zero] using hd'
    change (∫ x, g x * signDensity x ∂ν.totalVariation) = 0
    rw [LocallyFiniteSignedMeasure.totalVariation, integral_add_measure hintpos hintneg,
      hposint, hnegint]
    exact hreal
  have hfalse : ∀ᵐ x ∂ν.totalVariation, False := hsignzero.mono fun x hx => by
    have h := hsignnorm x
    rw [hx, norm_zero] at h
    norm_num at h
  have huniv : ν.totalVariation univ = 0 := by simpa only [ae_iff, not_false_eq_true,
    ofPred_true] using hfalse
  have hparts : ν.positive univ + ν.negative univ = 0 := by
    simpa only [LocallyFiniteSignedMeasure.totalVariation, Measure.add_apply] using huniv
  exact ⟨Measure.measure_univ_eq_zero.mp (add_eq_zero.mp hparts).1,
    Measure.measure_univ_eq_zero.mp (add_eq_zero.mp hparts).2⟩

private def faithfulnessBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

private theorem faithfulnessBump_radius_le_one (n : ℕ) : (faithfulnessBump n).rOut ≤ 1 := by
  dsimp [faithfulnessBump]
  exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    (by linarith [Nat.cast_nonneg (α := ℝ) n])

private def faithfulnessApprox (g : C_c(ℝ, ℝ)) (n : ℕ) : SchwartzMap ℝ ℂ :=
  ((show HasCompactSupport (Complex.ofRealCLM ∘ (faithfulnessBump n).normed volume) from
      (faithfulnessBump n).hasCompactSupport_normed.comp_left rfl).convolution
    (show HasCompactSupport (Complex.ofRealCLM ∘ (g : ℝ → ℝ)) from
      g.hasCompactSupport.comp_left rfl) (L := ContinuousLinearMap.mul ℂ ℂ)).toSchwartzMap
    ((show HasCompactSupport (Complex.ofRealCLM ∘ (faithfulnessBump n).normed volume) from
      (faithfulnessBump n).hasCompactSupport_normed.comp_left rfl).contDiff_convolution_left
      (ContinuousLinearMap.mul ℝ ℂ)
      (Complex.ofRealCLM.contDiff.comp (faithfulnessBump n).contDiff_normed)
      ((g.continuous.integrable_of_hasCompactSupport (μ := volume) g.hasCompactSupport).ofReal.locallyIntegrable))

private theorem faithfulnessApprox_eq_real_convolution (g : C_c(ℝ, ℝ)) (n : ℕ) (x : ℝ) :
    faithfulnessApprox g n x =
      ((faithfulnessBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y => (g y : ℂ))) x := by
  change (∫ t : ℝ, ((faithfulnessBump n).normed volume t : ℂ) * (g (x-t) : ℂ)) = _
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, Complex.real_smul]

private theorem faithfulnessApprox_tendsto (g : C_c(ℝ, ℝ)) (x : ℝ) :
    Tendsto (fun n => faithfulnessApprox g n x) atTop (𝓝 (g x : ℂ)) := by
  simp_rw [faithfulnessApprox_eq_real_convolution]
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (show Tendsto (fun n => (faithfulnessBump n).rOut) atTop (𝓝 0) from
      tendsto_one_div_add_atTop_nhds_zero_nat)
    (Complex.continuous_ofReal.comp g.continuous) x

/-- Positive locally finite measures are determined by their actual Schwartz
integrals, without requiring finite mass on the whole line. -/
theorem measure_eq_of_schwartz_integral_eq (μ η : Measure ℝ)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure η]
    (heq : ∀ f : SchwartzMap ℝ ℂ, (∫ x, f x ∂μ) = ∫ x, f x ∂η) : μ = η := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  obtain ⟨C, hC⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  let K : Set ℝ := Metric.closedBall 0 1 + tsupport g
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ) 1).add g.hasCompactSupport
  have hbound (n : ℕ) (x : ℝ) : ‖faithfulnessApprox g n x‖ ≤ K.indicator (fun _ => C) x := by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, faithfulnessApprox_eq_real_convolution, ← dist_zero_right]
      apply dist_convolution_le hC0 (faithfulnessBump n).support_normed_eq.subset
        (faithfulnessBump n).nonneg_normed (faithfulnessBump n).integral_normed
        (Complex.continuous_ofReal.comp g.continuous).aestronglyMeasurable
      intro y _
      simpa only [dist_zero_right, Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hC y
    · rw [indicator_of_notMem hx]
      have hzero : faithfulnessApprox g n x = 0 := by
        by_contra hne
        have hs : x ∈ Function.support
            ((Complex.ofRealCLM ∘ (faithfulnessBump n).normed volume) ⋆[ContinuousLinearMap.mul ℂ ℂ]
              (Complex.ofRealCLM ∘ (g : ℝ → ℝ))) := hne
        obtain ⟨a, ha, b, hb, hab⟩ := support_convolution_subset
          (L := ContinuousLinearMap.mul ℂ ℂ) hs
        apply hx
        refine ⟨a, ?_, b, ?_, hab⟩
        · have ha' : a ∈ Function.support ((faithfulnessBump n).normed volume) := by
            simpa only [Function.mem_support, Function.comp_apply, Complex.ofRealCLM_apply,
              Complex.ofReal_ne_zero] using ha
          rw [(faithfulnessBump n).support_normed_eq] at ha'
          exact Metric.ball_subset_closedBall (Metric.ball_subset_ball (faithfulnessBump_radius_le_one n) ha')
        · apply subset_closure
          simpa only [Function.mem_support, Function.comp_apply, Complex.ofRealCLM_apply,
            Complex.ofReal_ne_zero] using hb
      rw [hzero, norm_zero]
  have hlim (θ : Measure ℝ) [IsLocallyFiniteMeasure θ] :
      Tendsto (fun n => ∫ x, faithfulnessApprox g n x ∂θ) atTop (𝓝 (∫ x, (g x : ℂ) ∂θ)) := by
    apply tendsto_integral_of_dominated_convergence (K.indicator (fun _ => C))
    · intro n
      exact (faithfulnessApprox g n).continuous.aestronglyMeasurable
    · exact (integrableOn_const (μ := θ) (s := K) (C := C) hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
    · intro n
      exact Eventually.of_forall (hbound n)
    · exact Eventually.of_forall (faithfulnessApprox_tendsto g)
  have h := tendsto_nhds_unique (hlim μ)
    ((hlim η).congr' (Eventually.of_forall (fun n => (heq (faithfulnessApprox g n)).symm)))
  simpa only [integral_complex_ofReal, Complex.ofReal_inj] using h

private theorem jordan_positive_le_of_cross_sum
    (ν η : LocallyFiniteSignedMeasure) (heq : ν.positive + η.negative = η.positive + ν.negative) :
    ν.positive ≤ η.positive := by
  obtain ⟨s, hs, hps, hns⟩ := ν.mutuallySingular
  intro t
  have ht := congrArg (fun θ : Measure ℝ => θ (t ∩ sᶜ)) heq
  simp only [Measure.add_apply] at ht
  have hp : ν.positive (t ∩ sᶜ) = ν.positive t :=
    measure_inter_conull (by simpa only [compl_compl] using hps)
  have hn : ν.negative (t ∩ sᶜ) = 0 := measure_mono_null inter_subset_right hns
  rw [hp, hn, add_zero] at ht
  exact (le_add_of_nonneg_right (zero_le)).trans (ht.trans_le (measure_mono inter_subset_left))

private theorem jordan_negative_le_of_cross_sum
    (ν η : LocallyFiniteSignedMeasure) (heq : ν.positive + η.negative = η.positive + ν.negative) :
    ν.negative ≤ η.negative := by
  obtain ⟨s, hs, hps, hns⟩ := ν.mutuallySingular
  intro t
  have ht := congrArg (fun θ : Measure ℝ => θ (t ∩ s)) heq
  simp only [Measure.add_apply] at ht
  have hp : ν.positive (t ∩ s) = 0 := measure_mono_null inter_subset_right hps
  have hn : ν.negative (t ∩ s) = ν.negative t := measure_inter_conull hns
  rw [hp, hn, zero_add] at ht
  exact (le_add_of_nonneg_left (zero_le)).trans (ht.symm.trans_le (measure_mono inter_subset_left))

private theorem locallyFinite_add (μ η : Measure ℝ)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure η] : IsLocallyFiniteMeasure (μ + η) where
  finiteAtNhds x := by
    obtain ⟨s, hs, hsfinite⟩ := μ.finiteAt_nhds x
    obtain ⟨t, ht, htfinite⟩ := η.finiteAt_nhds x
    refine ⟨s ∩ t, Filter.inter_mem hs ht, ?_⟩
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr
      ⟨(measure_mono inter_subset_left).trans_lt hsfinite,
        (measure_mono inter_subset_right).trans_lt htfinite⟩

/-- Equality of the actual distributions recovers both Jordan measures.
The proof compares cross-sums of positive measures and uses mutual singularity;
it never cancels infinite global masses. -/
theorem LocallyFiniteSignedMeasure.parts_eq_of_distribution_eq
    (ν η : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) (hη : η.HasLinearGrowth)
    (heq : ν.distributionOfLinearGrowth hν = η.distributionOfLinearGrowth hη) :
    ν.positive = η.positive ∧ ν.negative = η.negative := by
  let := (ν.parts_temperate_of_linear_growth hν).1
  let := (ν.parts_temperate_of_linear_growth hν).2
  let := (η.parts_temperate_of_linear_growth hη).1
  let := (η.parts_temperate_of_linear_growth hη).2
  let := locallyFinite_add ν.positive η.negative
  let := locallyFinite_add η.positive ν.negative
  have hcross : ν.positive + η.negative = η.positive + ν.negative := by
    apply measure_eq_of_schwartz_integral_eq
    intro test
    rw [integral_add_measure (test.integrable (μ := ν.positive)) (test.integrable (μ := η.negative)),
      integral_add_measure (test.integrable (μ := η.positive)) (test.integrable (μ := ν.negative))]
    have h := congrArg (fun T : TemperedDistribution ℝ ℂ => T test) heq
    rw [ν.distributionOfLinearGrowth_apply, η.distributionOfLinearGrowth_apply] at h
    linear_combination h
  exact ⟨le_antisymm (jordan_positive_le_of_cross_sum ν η hcross)
      (jordan_positive_le_of_cross_sum η ν hcross.symm),
    le_antisymm (jordan_negative_le_of_cross_sum ν η hcross)
      (jordan_negative_le_of_cross_sum η ν hcross.symm)⟩

/-- The full faithful embedding of the linearly growing signed-measure class. -/
theorem LocallyFiniteSignedMeasure.distributionOfLinearGrowth_injective :
    Function.Injective (fun ν : {ν : LocallyFiniteSignedMeasure // ν.HasLinearGrowth} =>
      ν.val.distributionOfLinearGrowth ν.property) := by
  intro ν η heq
  apply Subtype.ext
  obtain ⟨hp, hn⟩ := ν.val.parts_eq_of_distribution_eq η.val ν.property η.property heq
  cases ν with | mk ν hν =>
    cases η with | mk η hη =>
      cases ν
      cases η
      cases hp
      cases hn
      rfl

#print axioms LocallyFiniteSignedMeasure.distributionOfLinearGrowth_injective
#print axioms quadraticDecay_integrable_of_linear_growth
#print axioms hasTemperateGrowth_of_linear_growth
#print axioms LocallyFiniteSignedMeasure.parts_eq_zero_of_distribution_eq_zero

end Zeta23.OPICA
