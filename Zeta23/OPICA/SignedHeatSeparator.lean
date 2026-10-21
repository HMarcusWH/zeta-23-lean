import Zeta23.OPICA.SincTriangle
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Jordan-measure support consequences for the sharp-gap separator

The signed-measure carrier permits infinite total variation on the whole
line. Compact smooth approximate identities justify the actual signed
sinc-squared/triangle pairing. Integer translation then forces every
lattice atom to vanish under the exact gap hypothesis.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap FourierTransform Convolution Topology

namespace Zeta23.OPICA

def integerLattice : Set ℝ := Set.range (fun n : ℤ => (n : ℝ))

theorem integerLattice_measurable : MeasurableSet integerLattice :=
  (Set.countable_range (fun n : ℤ => (n : ℝ))).measurableSet

/-- The Jordan parts of a signed measure with zero restriction to the unit
gap both have zero mass there. -/
def LocallyFiniteSignedMeasure.HasUnitGap (ν : LocallyFiniteSignedMeasure) : Prop :=
  ν.positive (Ioo (-1) 1) = 0 ∧ ν.negative (Ioo (-1) 1) = 0

/-- Off-lattice nonnegativity in Jordan coordinates. -/
def LocallyFiniteSignedMeasure.OffLatticeNonnegative (ν : LocallyFiniteSignedMeasure) : Prop :=
  ν.negative integerLatticeᶜ = 0

def LocallyFiniteSignedMeasure.FourierSelfdual (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) : Prop :=
  𝓕 (ν.distributionOfLinearGrowth hν) = ν.distributionOfLinearGrowth hν

theorem unitTriangle_integral_zero_of_gap (μ : Measure ℝ)
    (hgap : μ (Ioo (-1) 1) = 0) : (∫ x, unitTriangle x ∂μ) = 0 := by
  have hae : ∀ᵐ x ∂μ, x ∉ Ioo (-1 : ℝ) 1 := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hgap
  apply integral_eq_zero_of_ae
  filter_upwards [hae] with x hx
  apply unitTriangle_eq_zero_of_one_le_abs
  by_contra h
  exact hx (abs_lt.mp (lt_of_not_ge h))

theorem singleton_zero_of_unit_gap (μ : Measure ℝ)
    (hgap : μ (Ioo (-1) 1) = 0) : μ {0} = 0 := by
  apply measure_mono_null _ hgap
  intro x hx
  simp only [mem_singleton_iff] at hx
  subst x
  norm_num

/-- Sinc-squared vanishes almost everywhere for a lattice-supported measure
whose origin atom has zero mass. -/
theorem sincSquared_integral_zero_of_lattice_support (μ : Measure ℝ)
    (hlattice : μ integerLatticeᶜ = 0) (horigin : μ {0} = 0) :
    (∫ x, sincSquared x ∂μ) = 0 := by
  have hae : ∀ᵐ x ∂μ, x ∈ integerLattice := ae_iff.mpr hlattice
  have hne : ∀ᵐ x ∂μ, x ≠ 0 := by
    apply ae_iff.mpr
    simpa using horigin
  apply integral_eq_zero_of_ae
  filter_upwards [hae, hne] with x hx hxne
  obtain ⟨n, rfl⟩ := hx
  exact sincSquared_int_zero (by intro hn; subst n; exact hxne (by simp))

/-- Actual vanishing of the nonnegative sinc test forces off-lattice mass
to vanish. The integrability needed for this inference is proved from
linear growth, rather than included as a conclusion-shaped certificate. -/
theorem lattice_support_of_sincSquared_integral_zero (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] (hμ : LinearMassGrowth μ)
    (hzero : (∫ x, sincSquared x ∂μ) = 0) : μ integerLatticeᶜ = 0 := by
  have hsae : sincSquared =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg sincSquared_nonneg
      (sincSquared_integrable_of_linear_growth μ hμ)).mp hzero
  apply ae_iff.mp
  filter_upwards [hsae] with x hx
  by_contra hxlattice
  have hnotint : ¬ ∃ n : ℤ, (n : ℝ) = x := hxlattice
  have hpos := sincSquared_pos_off_lattice hnotint
  simp only [Pi.zero_apply] at hx
  linarith

/-- Integer translation of a Schwartz test does not change the values of
its Fourier transform at integer frequencies. This is a change of variables
in the actual Fourier integral, with the integer phase evaluated exactly. -/
theorem fourier_integerTranslate_at_integer (test : SchwartzMap ℝ ℂ) (k n : ℤ) :
    (𝓕 (test.compSubConstCLM ℂ (k : ℝ))) (n : ℝ) = (𝓕 test) (n : ℝ) := by
  change 𝓕 (test.compSubConstCLM ℂ (k : ℝ) : ℝ → ℂ) (n : ℝ) =
    𝓕 (test : ℝ → ℂ) (n : ℝ)
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, SchwartzMap.compSubConstCLM_apply]
  let F := fun x : ℝ => Complex.exp (((-2 * Real.pi * x * (n : ℝ)) : ℝ) * Complex.I) *
    test (x - (k : ℝ))
  change (∫ x : ℝ, F x) = _
  rw [← integral_add_right_eq_self F (k : ℝ)]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [F]
  have hexp : Complex.exp (((-2 * Real.pi * (x + (k : ℝ)) * (n : ℝ)) : ℝ) * Complex.I) =
      Complex.exp (((-2 * Real.pi * x * (n : ℝ)) : ℝ) * Complex.I) *
        Complex.exp (((-(k * n) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, Complex.exp_int_mul_two_pi_mul_I, mul_one, add_sub_cancel_right]

/-- A lattice-supported selfdual measure is periodic when tested against
Schwartz functions. Both integrations use the actual Jordan measures. -/
theorem LocallyFiniteSignedMeasure.integerTranslate_pairing
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth)
    (hself : ν.FourierSelfdual hν)
    (hpos : ν.positive integerLatticeᶜ = 0) (hneg : ν.negative integerLatticeᶜ = 0)
    (test : SchwartzMap ℝ ℂ) (k : ℤ) :
    ν.distributionOfLinearGrowth hν (test.compSubConstCLM ℂ (k : ℝ)) =
      ν.distributionOfLinearGrowth hν test := by
  have hposa : ∀ᵐ x ∂ν.positive, x ∈ integerLattice := ae_iff.mpr hpos
  have hnega : ∀ᵐ x ∂ν.negative, x ∈ integerLattice := ae_iff.mpr hneg
  have hshift : ν.distributionOfLinearGrowth hν (𝓕 (test.compSubConstCLM ℂ (k : ℝ))) =
      ν.distributionOfLinearGrowth hν (𝓕 test) := by
    rw [ν.distributionOfLinearGrowth_apply, ν.distributionOfLinearGrowth_apply]
    congr 1
    · apply integral_congr_ae
      filter_upwards [hposa] with x hx
      obtain ⟨n, rfl⟩ := hx
      exact fourier_integerTranslate_at_integer test k n
    · apply integral_congr_ae
      filter_upwards [hnega] with x hx
      obtain ⟨n, rfl⟩ := hx
      exact fourier_integerTranslate_at_integer test k n
  have hfixed (f : SchwartzMap ℝ ℂ) : ν.distributionOfLinearGrowth hν (𝓕 f) =
      ν.distributionOfLinearGrowth hν f := by
    exact congrArg (fun T : TemperedDistribution ℝ ℂ => T f) hself
  rw [hfixed, hfixed] at hshift
  exact hshift

/-- Compact approximate identities; the outer radii decrease to zero. -/
def separatorBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem separatorBump_radius_tendsto :
    Tendsto (fun n => (separatorBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem separatorBump_radius_le_one (n : ℕ) : (separatorBump n).rOut ≤ 1 := by
  dsimp [separatorBump]
  exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem regularizedTriangle_eq_real_convolution (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    regularizedTriangle φ x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y => (unitTriangle y : ℂ))) x := by
  change (∫ t : ℝ, (φ.normed volume t : ℂ) * (unitTriangle (x-t) : ℂ)) = _
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, Complex.real_smul]

theorem regularizedTriangle_tendsto (x : ℝ) :
    Tendsto (fun n => regularizedTriangle (separatorBump n) x) atTop
      (𝓝 (unitTriangle x : ℂ)) := by
  simp_rw [regularizedTriangle_eq_real_convolution]
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    separatorBump_radius_tendsto
    (Complex.continuous_ofReal.comp unitTriangle_continuous) x

theorem normalizedComplexBump_fourier_tendsto (xi : ℝ) :
    Tendsto (fun n => 𝓕 (normalizedComplexBump (separatorBump n)) xi) atTop (𝓝 1) := by
  let phase : ℝ → ℂ := fun x => Complex.exp ((2*Real.pi*x*xi : ℝ)*Complex.I)
  have hphase : Continuous phase := by fun_prop
  have heq (φ : ContDiffBump (0 : ℝ)) : 𝓕 (normalizedComplexBump φ) xi =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] phase) 0 := by
    rw [Real.fourier_real_eq_integral_exp_smul, convolution_def]
    apply integral_congr_ae
    filter_upwards with t
    simp only [normalizedComplexBump, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul, Complex.real_smul, phase, zero_sub]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  simp_rw [heq]
  simpa [phase] using ContDiffBump.convolution_tendsto_right_of_continuous
    separatorBump_radius_tendsto hphase (0 : ℝ)

theorem regularizedTriangle_fourier_tendsto (xi : ℝ) :
    Tendsto (fun n => 𝓕 (regularizedTriangle (separatorBump n) : ℝ → ℂ) xi) atTop
      (𝓝 (sincSquared xi : ℂ)) := by
  simp_rw [regularizedTriangle_fourier]
  simpa using (normalizedComplexBump_fourier_tendsto xi).mul_const (sincSquared xi : ℂ)

theorem unitTriangle_norm_le_one (x : ℝ) : ‖(unitTriangle x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unitTriangle_nonneg x)]
  exact max_le (by linarith [abs_nonneg x]) (by norm_num)

theorem regularizedTriangle_norm_le_one (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    ‖regularizedTriangle φ x‖ ≤ 1 := by
  rw [regularizedTriangle_eq_real_convolution, ← dist_zero_right]
  exact dist_convolution_le (by norm_num) φ.support_normed_eq.subset φ.nonneg_normed
    φ.integral_normed
    (Complex.continuous_ofReal.comp unitTriangle_continuous).aestronglyMeasurable
    (fun y _ => by simpa only [dist_zero_right] using unitTriangle_norm_le_one y)

theorem regularizedTriangle_zero_of_two_le_abs (n : ℕ) {x : ℝ} (hx : 2 ≤ |x|) :
    regularizedTriangle (separatorBump n) x = 0 := by
  by_contra hne
  have hs : x ∈ Function.support
      (normalizedComplexBump (separatorBump n) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun y => (unitTriangle y : ℂ))) := hne
  obtain ⟨a, ha, b, hb, hab⟩ := support_convolution_subset
    (L := ContinuousLinearMap.mul ℂ ℂ) hs
  have ha' : a ∈ Function.support ((separatorBump n).normed volume) := by
    simpa only [Function.mem_support, normalizedComplexBump, Complex.ofReal_ne_zero] using ha
  rw [(separatorBump n).support_normed_eq] at ha'
  have haabs : |a| < 1 := lt_of_lt_of_le
    (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ha')
    (separatorBump_radius_le_one n)
  have hbabs : |b| < 1 := by
    by_contra hb'
    exact hb (by change (unitTriangle b : ℂ) = 0; rw [unitTriangle_eq_zero_of_one_le_abs (le_of_not_gt hb')]; rfl)
  have habs : |x| < 2 := by
    rw [← hab]
    exact lt_of_le_of_lt (abs_add_le a b) (by linarith)
  linarith

theorem regularizedTriangle_norm_le_indicator (n : ℕ) (x : ℝ) :
    ‖regularizedTriangle (separatorBump n) x‖ ≤ (Icc (-2 : ℝ) 2).indicator (fun _ => 1) x := by
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · rw [indicator_of_mem hx]
    exact regularizedTriangle_norm_le_one _ _
  · rw [indicator_of_notMem hx]
    rw [regularizedTriangle_zero_of_two_le_abs n (by
      by_contra h
      exact hx (by have h' := abs_lt.mp (lt_of_not_ge h); constructor <;> linarith)), norm_zero]

theorem signed_sinc_triangle_pairing (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) :
    ν.integral sincSquared = ν.integral unitTriangle := by
  have hleft (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (hμ : LinearMassGrowth μ) :
      Tendsto (fun n => ∫ x, 𝓕 (regularizedTriangle (separatorBump n) : ℝ → ℂ) x ∂μ)
        atTop (𝓝 (∫ x, (sincSquared x : ℂ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence sincSquared
    · intro n
      exact (𝓕 (regularizedTriangle (separatorBump n))).continuous.aestronglyMeasurable
    · exact sincSquared_integrable_of_linear_growth μ hμ
    · intro n
      exact Eventually.of_forall (regularizedTriangle_fourier_norm_le _)
    · exact Eventually.of_forall regularizedTriangle_fourier_tendsto
  have hright (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
      Tendsto (fun n => ∫ x, regularizedTriangle (separatorBump n) x ∂μ)
        atTop (𝓝 (∫ x, (unitTriangle x : ℂ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence ((Icc (-2 : ℝ) 2).indicator (fun _ => 1))
    · intro n
      exact (regularizedTriangle (separatorBump n)).continuous.aestronglyMeasurable
    · exact (integrableOn_const (μ := μ) (s := Icc (-2 : ℝ) 2) (C := (1 : ℝ))
        isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
    · intro n
      exact Eventually.of_forall (regularizedTriangle_norm_le_indicator n)
    · exact Eventually.of_forall regularizedTriangle_tendsto
  have hL := (hleft ν.positive (ν.positive_hasLinearGrowth hν)).sub
    (hleft ν.negative (ν.negative_hasLinearGrowth hν))
  have hR := (hright ν.positive).sub (hright ν.negative)
  have heq (n : ℕ) :
      (∫ x, 𝓕 (regularizedTriangle (separatorBump n) : ℝ → ℂ) x ∂ν.positive) -
        (∫ x, 𝓕 (regularizedTriangle (separatorBump n) : ℝ → ℂ) x ∂ν.negative) =
      (∫ x, regularizedTriangle (separatorBump n) x ∂ν.positive) -
        (∫ x, regularizedTriangle (separatorBump n) x ∂ν.negative) :=
    congrArg (fun T : TemperedDistribution ℝ ℂ => T (regularizedTriangle (separatorBump n))) hself
  have hc := tendsto_nhds_unique hL (hR.congr' (Eventually.of_forall (fun n => (heq n).symm)))
  simp only [integral_complex_ofReal, ← Complex.ofReal_sub, Complex.ofReal_inj] at hc
  exact hc

def latticeAtomBump : ContDiffBump (0 : ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def latticeAtomTest : SchwartzMap ℝ ℂ :=
  (show HasCompactSupport (Complex.ofRealCLM ∘ (latticeAtomBump : ℝ → ℝ)) from
    latticeAtomBump.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp latticeAtomBump.contDiff)

theorem latticeAtomTest_at_integer (n : ℤ) :
    latticeAtomTest (n : ℝ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl, Int.cast_zero]
    change (latticeAtomBump (0 : ℝ) : ℂ) = 1
    rw [latticeAtomBump.one_of_mem_closedBall (by simp [latticeAtomBump])]
    rfl
  · rw [if_neg hn]
    change (latticeAtomBump (n : ℝ) : ℂ) = 0
    have h : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    rw [latticeAtomBump.zero_of_le_dist (by
      simpa only [latticeAtomBump, dist_zero_right, Real.norm_eq_abs] using
        (show (1/2 : ℝ) ≤ |(n : ℝ)| by linarith))]
    rfl

theorem latticeAtomTest_integral (μ : Measure ℝ) (hsupport : μ integerLatticeᶜ = 0) (k : ℤ) :
    (∫ x, (latticeAtomTest.compSubConstCLM ℂ (k : ℝ)) x ∂μ) =
      (μ.real {(k : ℝ)} : ℂ) := by
  have hae : ∀ᵐ x ∂μ, x ∈ integerLattice := ae_iff.mpr hsupport
  have heq : (latticeAtomTest.compSubConstCLM ℂ (k : ℝ) : ℝ → ℂ) =ᵐ[μ]
      ({(k : ℝ)} : Set ℝ).indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [hae] with x hx
    obtain ⟨n, rfl⟩ := hx
    rw [SchwartzMap.compSubConstCLM_apply]
    have hcast : (n : ℝ) - (k : ℝ) = ((n-k : ℤ) : ℝ) := by norm_cast
    rw [hcast, latticeAtomTest_at_integer]
    by_cases hnk : n = k
    · subst n
      simp
    · have hcastne : (n : ℝ) ≠ (k : ℝ) := by exact_mod_cast hnk
      simp [sub_ne_zero.mpr hnk, hcastne]
  rw [integral_congr_ae heq, integral_indicator (measurableSet_singleton _), integral_const]
  simp only [measureReal_restrict_apply_univ, Complex.real_smul, mul_one]

theorem measure_zero_of_lattice_support_atoms_zero (μ : Measure ℝ)
    (hsupport : μ integerLatticeᶜ = 0) (hatoms : ∀ n : ℤ, μ {(n : ℝ)} = 0) : μ = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have hlattice : μ integerLattice = 0 := by
    have heq : integerLattice = ⋃ n : ℤ, ({(n : ℝ)} : Set ℝ) := by
      ext x
      simp [integerLattice]
    rw [heq]
    exact measure_iUnion_null hatoms
  have h := measure_union_le integerLattice integerLatticeᶜ (μ := μ)
  rw [union_compl_self, hlattice, hsupport, add_zero] at h
  exact le_antisymm h (zero_le)

/-- The sharp-gap conclusion for the full locally finite Jordan-pair carrier.
Both Jordan measures vanish, so the represented signed measure is zero. -/
theorem signed_sharp_gap_separator (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν)
    (hgap : ν.HasUnitGap) (hoff : ν.OffLatticeNonnegative) :
    ν.positive = 0 ∧ ν.negative = 0 := by
  have hpair := signed_sinc_triangle_pairing ν hν hself
  have hnegative : (∫ x, sincSquared x ∂ν.negative) = 0 :=
    sincSquared_integral_zero_of_lattice_support ν.negative hoff
      (singleton_zero_of_unit_gap ν.negative hgap.2)
  have hpositive : (∫ x, sincSquared x ∂ν.positive) = 0 := by
    change (∫ x, sincSquared x ∂ν.positive) - (∫ x, sincSquared x ∂ν.negative) =
      (∫ x, unitTriangle x ∂ν.positive) - (∫ x, unitTriangle x ∂ν.negative) at hpair
    rw [hnegative, unitTriangle_integral_zero_of_gap ν.positive hgap.1,
      unitTriangle_integral_zero_of_gap ν.negative hgap.2] at hpair
    simpa using hpair
  have hpossupport := lattice_support_of_sincSquared_integral_zero ν.positive
    (ν.positive_hasLinearGrowth hν) hpositive
  have heq (n : ℤ) : ν.positive.real {(n : ℝ)} = ν.negative.real {(n : ℝ)} := by
    have hperiod := ν.integerTranslate_pairing hν hself hpossupport hoff latticeAtomTest n
    have hzero (μ : Measure ℝ) (hs : μ integerLatticeᶜ = 0) :
        (∫ x, latticeAtomTest x ∂μ) = (μ.real {0} : ℂ) := by
      simpa only [SchwartzMap.compSubConstCLM_apply, Int.cast_zero, sub_zero] using
        latticeAtomTest_integral μ hs 0
    simp only [ν.distributionOfLinearGrowth_apply] at hperiod
    rw [latticeAtomTest_integral ν.positive hpossupport n,
      latticeAtomTest_integral ν.negative hoff n, hzero ν.positive hpossupport,
      hzero ν.negative hoff] at hperiod
    have hp0 : ν.positive.real {0} = 0 := by
      simp only [Measure.real, singleton_zero_of_unit_gap ν.positive hgap.1, ENNReal.toReal_zero]
    have hn0 : ν.negative.real {0} = 0 := by
      simp only [Measure.real, singleton_zero_of_unit_gap ν.negative hgap.2, ENNReal.toReal_zero]
    rw [hp0, hn0, Complex.ofReal_zero, sub_self] at hperiod
    exact Complex.ofReal_inj.mp (sub_eq_zero.mp hperiod)
  have hatoms (n : ℤ) : ν.positive {(n : ℝ)} = 0 ∧ ν.negative {(n : ℝ)} = 0 := by
    obtain ⟨s, hs, hps, hns⟩ := ν.mutuallySingular
    have he := heq n
    have hpn : ν.positive {(n : ℝ)} ≠ ⊤ := isCompact_singleton.measure_lt_top.ne
    have hnn : ν.negative {(n : ℝ)} ≠ ⊤ := isCompact_singleton.measure_lt_top.ne
    by_cases hn : (n : ℝ) ∈ s
    · have hp : ν.positive {(n : ℝ)} = 0 :=
        measure_mono_null (singleton_subset_iff.mpr hn) hps
      refine ⟨hp, ?_⟩
      exact ((ENNReal.toReal_eq_zero_iff _).mp (by
        simpa only [Measure.real, hp, ENNReal.toReal_zero] using he.symm)).resolve_right hnn
    · have hm : ν.negative {(n : ℝ)} = 0 :=
        measure_mono_null (singleton_subset_iff.mpr hn) hns
      refine ⟨?_, hm⟩
      exact ((ENNReal.toReal_eq_zero_iff _).mp (by
        simpa only [Measure.real, hm, ENNReal.toReal_zero] using he)).resolve_right hpn
  exact ⟨measure_zero_of_lattice_support_atoms_zero ν.positive hpossupport (fun n => (hatoms n).1),
    measure_zero_of_lattice_support_atoms_zero ν.negative hoff (fun n => (hatoms n).2)⟩

/-- The finite region at distance at least `d` from every integer. -/
def signedBudgetRegion (R d : ℝ) : Set ℝ :=
  {x | |x| ≤ R ∧ d ≤ Metric.infDist x integerLattice}

theorem signedBudgetRegion_measurable (R d : ℝ) : MeasurableSet (signedBudgetRegion R d) :=
  ((isClosed_le continuous_abs continuous_const).inter
    (isClosed_le continuous_const (Metric.continuous_infDist_pt integerLattice))).measurableSet

theorem signedBudgetRegion_finite (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] (R d : ℝ) :
    μ (signedBudgetRegion R d) < ⊤ := by
  calc
    _ ≤ μ (Icc (-R) R) := measure_mono (fun _ hx => abs_le.mp hx.1)
    _ < ⊤ := isCompact_Icc.measure_lt_top

theorem signedBudgetRegion_integer_distance {R d x : ℝ}
    (hx : x ∈ signedBudgetRegion R d) (n : ℤ) : d ≤ |x-(n : ℝ)| := by
  exact hx.2.trans (by simpa only [Real.dist_eq] using
    Metric.infDist_le_dist_of_mem (show (n : ℝ) ∈ integerLattice from ⟨n, rfl⟩))

theorem sine_abs_lower_of_integer_distance {d x : ℝ} (hd : 0 < d)
    (hxd : ∀ n : ℤ, d ≤ |x-(n : ℝ)|) : 2*d ≤ |Real.sin (Real.pi*x)| := by
  let r := Int.fract x
  have hr0 : 0 ≤ r := Int.fract_nonneg x
  have hr1 : r < 1 := Int.fract_lt_one x
  have hdr : d ≤ r := by
    have h := hxd (Int.floor x)
    change d ≤ |r| at h
    rwa [abs_of_nonneg hr0] at h
  have hdr' : d ≤ 1-r := by
    have hdist := hxd (Int.floor x + 1)
    have heq : x - ((Int.floor x + 1 : ℤ) : ℝ) = -(1-r) := by
      change x - ((Int.floor x + 1 : ℤ) : ℝ) = -(1-(x-(Int.floor x : ℝ)))
      push_cast
      ring
    rw [heq, abs_neg, abs_of_pos (by linarith : 0 < 1-r)] at hdist
    exact hdist
  have hsin : 2*d ≤ Real.sin (Real.pi*r) := by
    by_cases hrhalf : r ≤ 1/2
    · have h := Real.mul_le_sin (x := Real.pi*r)
        (mul_nonneg Real.pi_pos.le hr0) (by
          calc Real.pi*r ≤ Real.pi*(1/2) := mul_le_mul_of_nonneg_left hrhalf Real.pi_pos.le
            _ = Real.pi/2 := by ring)
      have hcancel : 2 / Real.pi * (Real.pi*r) = 2*r := by field_simp
      rw [hcancel] at h
      linarith
    · have h := Real.mul_le_sin (x := Real.pi*(1-r))
        (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr1.le)) (by
          calc Real.pi*(1-r) ≤ Real.pi*(1/2) :=
              mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
            _ = Real.pi/2 := by ring)
      have harg : Real.pi*(1-r) = Real.pi-Real.pi*r := by ring
      have hcancel : 2 / Real.pi * (Real.pi*(1-r)) = 2*(1-r) := by field_simp
      rw [hcancel, harg, Real.sin_pi_sub] at h
      linarith
  have hperiod := congrArg abs (Real.sin_sub_int_mul_pi (Real.pi*x) (Int.floor x))
  have harg : Real.pi*x-(Int.floor x : ℝ)*Real.pi = Real.pi*r := by
    change Real.pi*x-(Int.floor x : ℝ)*Real.pi = Real.pi*(x-(Int.floor x : ℝ))
    ring
  rw [harg, abs_mul, abs_neg_one_zpow, one_mul,
    abs_of_nonneg (by linarith : 0 ≤ Real.sin (Real.pi*r))] at hperiod
  exact hsin.trans_eq hperiod

theorem sincSquared_lower_on_signedBudgetRegion {R d x : ℝ} (hR : 1 ≤ R)
    (hd : 0 < d) (hx : x ∈ signedBudgetRegion R d) :
    4*d^2 / (Real.pi^2*R^2) ≤ sincSquared x := by
  have hdist := signedBudgetRegion_integer_distance hx
  have hsin := sine_abs_lower_of_integer_distance hd hdist
  have hxne : x ≠ 0 := by
    intro hxzero
    have h := hdist 0
    simp [hxzero] at h
    linarith
  have hid : sincSquared x * x^2 * Real.pi^2 = Real.sin (Real.pi*x)^2 := by
    rw [sincSquared, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxne), div_pow]
    field_simp
  have hxR : x^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx.1 2
  have hsquare : 4*d^2 ≤ Real.sin (Real.pi*x)^2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2*d) hsin 2
    nlinarith [sq_abs (Real.sin (Real.pi*x))]
  apply (div_le_iff₀ (by positivity : 0 < Real.pi^2*R^2)).mpr
  calc
    4*d^2 ≤ Real.sin (Real.pi*x)^2 := hsquare
    _ = sincSquared x*x^2*Real.pi^2 := hid.symm
    _ ≤ sincSquared x*R^2*Real.pi^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxR (sincSquared_nonneg x)) (sq_nonneg _)
    _ = sincSquared x*(Real.pi^2*R^2) := by ring

theorem sincSquared_integral_compl_lattice (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    (hμ : LinearMassGrowth μ) (horigin : μ {0} = 0) :
    (∫ x in integerLatticeᶜ, sincSquared x ∂μ) = ∫ x, sincSquared x ∂μ := by
  have hz : (∫ x in integerLattice, sincSquared x ∂μ) = 0 := by
    apply sincSquared_integral_zero_of_lattice_support
    · rw [Measure.restrict_apply integerLattice_measurable.compl, compl_inter_self, measure_empty]
    · rw [Measure.restrict_apply (measurableSet_singleton _)]
      exact measure_mono_null inter_subset_left horigin
  simpa only [hz, zero_add] using integral_add_compl integerLattice_measurable
    (sincSquared_integrable_of_linear_growth μ hμ)

/-- The global negative weighted mass pays for positive mass in the finite
region away from the lattice, with the paper's exact quantitative constant. -/
theorem signed_gap_negative_weighted_mass_budget (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) (hgap : ν.HasUnitGap)
    {R d : ℝ} (hR : 1 ≤ R) (hd : 0 < d) (_hdhalf : d ≤ 1/2) :
    (4*d^2 / (Real.pi^2*R^2)) * ν.positive.real (signedBudgetRegion R d) ≤
      ∫ x in integerLatticeᶜ, sincSquared x ∂ν.negative := by
  have hpair := signed_sinc_triangle_pairing ν hν hself
  change (∫ x, sincSquared x ∂ν.positive) - (∫ x, sincSquared x ∂ν.negative) =
    (∫ x, unitTriangle x ∂ν.positive) - (∫ x, unitTriangle x ∂ν.negative) at hpair
  rw [unitTriangle_integral_zero_of_gap ν.positive hgap.1,
    unitTriangle_integral_zero_of_gap ν.negative hgap.2, sub_self] at hpair
  have heq := sub_eq_zero.mp hpair
  rw [sincSquared_integral_compl_lattice ν.negative (ν.negative_hasLinearGrowth hν)
    (singleton_zero_of_unit_gap ν.negative hgap.2), ← heq]
  have hi := sincSquared_integrable_of_linear_growth ν.positive (ν.positive_hasLinearGrowth hν)
  calc
    _ = ∫ x in signedBudgetRegion R d, (4*d^2 / (Real.pi^2*R^2)) ∂ν.positive := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in signedBudgetRegion R d, sincSquared x ∂ν.positive := by
      apply setIntegral_mono_on
      · exact integrableOn_const (signedBudgetRegion_finite ν.positive R d).ne
      · exact hi.integrableOn
      · exact signedBudgetRegion_measurable R d
      · intro x hx
        exact sincSquared_lower_on_signedBudgetRegion hR hd hx
    _ ≤ ∫ x, sincSquared x ∂ν.positive :=
      setIntegral_le_integral hi (Eventually.of_forall sincSquared_nonneg)

/-- In addition to the sharp weighted estimate, the whole negative mass
off the lattice pays this budget, including when that mass is infinite. -/
theorem signed_gap_negative_mass_budget (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) (hgap : ν.HasUnitGap)
    {R d : ℝ} (hR : 1 ≤ R) (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    (4*d^2 / (Real.pi^2*R^2)) * ν.positive.real (signedBudgetRegion R d) ≤
        ∫ x in integerLatticeᶜ, sincSquared x ∂ν.negative ∧
      ENNReal.ofReal ((4*d^2 / (Real.pi^2*R^2)) *
        ν.positive.real (signedBudgetRegion R d)) ≤ ν.negative integerLatticeᶜ := by
  have hweighted := signed_gap_negative_weighted_mass_budget ν hν hself hgap hR hd hdhalf
  refine ⟨hweighted, ?_⟩
  by_cases hmass : ν.negative integerLatticeᶜ = ⊤
  · rw [hmass]
    exact le_top
  · let : IsFiniteMeasure (ν.negative.restrict integerLatticeᶜ) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hmass⟩
    have hbound : (∫ x in integerLatticeᶜ, sincSquared x ∂ν.negative) ≤
        ν.negative.real integerLatticeᶜ := by
      calc
        _ ≤ ∫ _x in integerLatticeᶜ, (1 : ℝ) ∂ν.negative :=
          integral_mono
            (sincSquared_integrable_of_linear_growth ν.negative
              (ν.negative_hasLinearGrowth hν)).integrableOn
            (integrable_const 1) sincSquared_le_one
        _ = _ := by simp only [setIntegral_const, smul_eq_mul, mul_one]
    exact (ENNReal.ofReal_le_iff_le_toReal hmass).mpr (hweighted.trans hbound)

end Zeta23.OPICA

#print axioms Zeta23.OPICA.signed_sinc_triangle_pairing
#print axioms Zeta23.OPICA.signed_sharp_gap_separator
#print axioms Zeta23.OPICA.signed_gap_negative_mass_budget
