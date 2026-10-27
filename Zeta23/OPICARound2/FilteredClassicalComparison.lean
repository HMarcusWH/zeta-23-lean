import Zeta23.OPICARound2.FixedFilter
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Zeta23.OPICAFollowup.SawtoothForce

/-!
# The literal fractional-part comparison

The actual logarithmic L2 equivalence is imported through ClassicalAdapter.
The classical indicator, fractional-part dictionary and exact pole-moment
tail cancellation retain their original normalizations. Full native
factorization and the comparison norm are separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped Topology

namespace Zeta23.OPICARound2

def probeReflection : ProbeL2 →ₗᵢ[ℂ] ProbeL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => -t) (Measure.measurePreserving_neg volume)

theorem probeReflection_coeFn (f : ProbeL2) :
    probeReflection f =ᵐ[volume] fun t : ℝ => f (-t) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

theorem probeReflection_involutive (f : ProbeL2) : probeReflection (probeReflection f) = f := by
  apply Lp.ext
  have hi := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
    (probeReflection_coeFn f)
  filter_upwards [probeReflection_coeFn (probeReflection f), hi] with t ht hi
  dsimp only [Function.comp_def] at hi
  rw [ht, hi]
  simp

private theorem full_delay_inverse (s : ℝ) (g : ProbeL2) :
    CCM.nativeCompletionL2Delay s (CCM.nativeCompletionL2Delay (-s) g) = g := by
  apply Lp.ext
  have hi := (measurePreserving_sub_right volume s).quasiMeasurePreserving.ae_eq
    (CCM.nativeCompletionL2Delay_coeFn (-s) g)
  filter_upwards [CCM.nativeCompletionL2Delay_coeFn s (CCM.nativeCompletionL2Delay (-s) g),
    hi] with t ht hi
  dsimp only [Function.comp_def] at hi
  rw [ht, hi]
  congr 1
  ring

private theorem full_delay_inner (s : ℝ) (f g : ProbeL2) :
    inner ℂ (CCM.nativeCompletionL2Delay s f) g =
      inner ℂ f (CCM.nativeCompletionL2Delay (-s) g) := by
  calc
    _ = inner ℂ (CCM.nativeCompletionL2Delay s f)
        (CCM.nativeCompletionL2Delay s (CCM.nativeCompletionL2Delay (-s) g)) := by
      rw [full_delay_inverse]
    _ = _ := (CCM.nativeCompletionL2Delay s).inner_map_map f (CCM.nativeCompletionL2Delay (-s) g)

private theorem reflection_delay_reflection (s : ℝ) (g : ProbeL2) :
    probeReflection (CCM.nativeCompletionL2Delay s (probeReflection g)) =
      CCM.nativeCompletionL2Delay (-s) g := by
  apply Lp.ext
  have hd := (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq
    (CCM.nativeCompletionL2Delay_coeFn s (probeReflection g))
  have hj := ((measurePreserving_sub_right volume s).comp
    (Measure.measurePreserving_neg volume)).quasiMeasurePreserving.ae_eq (probeReflection_coeFn g)
  filter_upwards [probeReflection_coeFn (CCM.nativeCompletionL2Delay s (probeReflection g)),
    hd, hj, CCM.nativeCompletionL2Delay_coeFn (-s) g] with t ht hd hj hg
  dsimp only [Function.comp_def] at hd hj
  rw [ht, hd, hj, hg]
  congr 1
  ring

def fullAntiInnerOperator : ProbeL2 →L[ℂ] ProbeL2 :=
  probeReflection.toContinuousLinearMap.comp
    (fullCausalInnerOperator.comp probeReflection.toContinuousLinearMap)

theorem fullAntiInnerOperator_norm (g : ProbeL2) : ‖fullAntiInnerOperator g‖ = ‖g‖ := by
  change ‖probeReflection (fullCausalInnerOperator (probeReflection g))‖ = ‖g‖
  rw [probeReflection.norm_map, fullCausalInnerOperator_norm, probeReflection.norm_map]

theorem fullCausalInnerOperator_adjoint :
    ContinuousLinearMap.adjoint fullCausalInnerOperator = fullAntiInnerOperator := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  let J : ProbeL2 →L[ℂ] ProbeL2 := probeReflection.toContinuousLinearMap
  have hpoint (s : ℝ) :
      inner ℂ (kernelL2Integrand causalInnerKernel f s) g =
        inner ℂ f (J (kernelL2Integrand causalInnerKernel (probeReflection g) s)) := by
    unfold kernelL2Integrand OPICAFollowup.causalFilterL2Integrand
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
      RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, inner_smul_right]
    change star (causalInnerKernel s : ℂ) * inner ℂ (CCM.nativeCompletionL2Delay s f) g =
      (causalInnerKernel s : ℂ) * inner ℂ f
        (probeReflection (CCM.nativeCompletionL2Delay s (probeReflection g)))
    rw [reflection_delay_reflection, full_delay_inner]
    simp
  have hi := kernelL2Integrand_integrable causalInnerKernel causalInnerKernel_integrable f
  have hj := kernelL2Integrand_integrable causalInnerKernel causalInnerKernel_integrable
    (probeReflection g)
  have hint := integral_congr_ae (μ := (volume : Measure ℝ)) (Filter.Eventually.of_forall hpoint)
  have hleft : (∫ s : ℝ, inner ℂ (kernelL2Integrand causalInnerKernel f s) g) =
      inner ℂ (∫ s : ℝ, kernelL2Integrand causalInnerKernel f s) g := by
    have h := congrArg (starRingEnd ℂ) (integral_inner (𝕜 := ℂ) hi g)
    rw [← integral_conj] at h
    simpa only [inner_conj_symm] using h
  rw [hleft, integral_inner (𝕜 := ℂ) (J.integrable_comp hj) f,
    J.integral_comp_comm hj] at hint
  change inner ℂ (f - kernelL2Operator causalInnerKernel causalInnerKernel_integrable f) g =
    inner ℂ f (probeReflection (probeReflection g -
      kernelL2Operator causalInnerKernel causalInnerKernel_integrable (probeReflection g)))
  rw [map_sub, probeReflection_involutive, inner_sub_left, inner_sub_right]
  exact congrArg (fun z : ℂ => inner ℂ f g - z) hint

theorem fullCausalInnerOperator_surjective : Function.Surjective fullCausalInnerOperator := by
  have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self fullAntiInnerOperator).mp
    fullAntiInnerOperator_norm
  rw [← fullCausalInnerOperator_adjoint, ContinuousLinearMap.adjoint_adjoint] at h
  intro g
  refine ⟨ContinuousLinearMap.adjoint fullCausalInnerOperator g, ?_⟩
  exact congrArg (fun T : ProbeL2 →L[ℂ] ProbeL2 => T g) h

def fullCausalInnerIsometry : ProbeL2 →ₗᵢ[ℂ] ProbeL2 where
  toLinearMap := fullCausalInnerOperator.toLinearMap
  norm_map' := fullCausalInnerOperator_norm

/-- Full-line onto unitarity is proved separately from the proper causal range. -/
def fullCausalInnerEquiv : ProbeL2 ≃ₗᵢ[ℂ] ProbeL2 :=
  LinearIsometryEquiv.ofSurjective fullCausalInnerIsometry fullCausalInnerOperator_surjective

/-- The actual classical indicator and fractional-part dictionary. -/
def classicalChi (x : ℝ) : ℂ := if x ∈ Ioo 0 1 then 1 else 0

def classicalRho (n : ℕ) (x : ℝ) : ℂ := ((Int.fract (1 / ((n : ℝ) * x)) : ℝ) : ℂ)

def classicalFiniteResidual {N : ℕ} (coeff : Fin N → ℂ) (x : ℝ) : ℂ :=
  classicalChi x + ∑ i : Fin N, coeff i * classicalRho (i.val + 1) x

theorem classicalRho_eq_reciprocal {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    classicalRho n x = 1 / ((n : ℂ) * (x : ℂ)) := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp : 1 < (n : ℝ) * x := by nlinarith
  have hnonneg : 0 ≤ 1 / ((n : ℝ) * x) := by positivity
  have hlt : 1 / ((n : ℝ) * x) < 1 := by
    exact (div_lt_one (by linarith)).mpr hp
  rw [classicalRho, Int.fract_eq_self.mpr ⟨hnonneg, hlt⟩]
  push_cast
  rfl

/-- The pole-moment condition cancels the entire x>1 tail pointwise. -/
theorem classicalFiniteResidual_zero_above_one {N : ℕ} (coeff : Fin N → ℂ)
    (hmoment : ∑ i : Fin N, coeff i / ((i.val + 1 : ℕ) : ℂ) = 0)
    {x : ℝ} (hx : 1 < x) : classicalFiniteResidual coeff x = 0 := by
  have hchi : classicalChi x = 0 := by
    simp [classicalChi, show x ∉ Ioo (0 : ℝ) 1 from fun h => (not_lt_of_ge hx.le) h.2]
  unfold classicalFiniteResidual
  rw [hchi, zero_add]
  have hpoint (i : Fin N) : classicalRho (i.val + 1) x =
      1 / (((i.val + 1 : ℕ) : ℂ) * (x : ℂ)) :=
    classicalRho_eq_reciprocal (by omega) hx
  simp_rw [hpoint]
  calc
    _ = (∑ i : Fin N, coeff i / ((i.val + 1 : ℕ) : ℂ)) / (x : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hmoment]; simp

theorem classicalChi_measurable : Measurable classicalChi :=
  Measurable.ite measurableSet_Ioo measurable_const measurable_const

theorem classicalRho_measurable (n : ℕ) : Measurable (classicalRho n) := by
  exact (measurable_fract.comp
    (measurable_const.div (measurable_const.mul measurable_id))).complex_ofReal

theorem reversedLogUnitary_classicalChi :
    reversedLogUnitary classicalChi =ᵐ[volume] fun t => (causalInnerKernel t : ℂ) := by
  have hzero : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [ae_iff]
    have heq : {t : ℝ | ¬t ≠ 0} = {0} := by ext t; simp
    rw [heq]
    exact measure_singleton (0 : ℝ)
  filter_upwards [hzero] with t ht
  by_cases hp : 0 < t
  · have he : Real.exp (-t) ∈ Ioo (0 : ℝ) 1 :=
      ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
    simp [reversedLogUnitary, classicalChi, he, causalInnerKernel, hp.le]
  · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hp) ht
    have he : Real.exp (-t) ∉ Ioo (0 : ℝ) 1 := by
      intro h
      have hb : 1 ≤ Real.exp (-t) := Real.one_le_exp_iff.mpr (by linarith)
      linarith [h.2]
    simp [reversedLogUnitary, classicalChi, he, causalInnerKernel, not_le_of_gt htneg]

/-- Exact whole-line dictionary conversion. The negative-time portion of
the fractional-part function is still present in the physical sawtooth. -/
theorem reversedLogUnitary_classicalRho {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    reversedLogUnitary (classicalRho n) t =
      (CCM.nativeIntegerCoefficient n : ℂ) * OPICAFollowup.sawtoothWeight (t - Real.log n) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hroot : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnreal]
    congr 1
    ring
  have harg : 1 / ((n : ℝ) * Real.exp (-t)) = Real.exp (t - Real.log n) := by
    rw [Real.exp_sub, Real.exp_log hnreal, Real.exp_neg]
    field_simp
  have he : CCM.nativeIntegerCoefficient n * Real.exp (-(t - Real.log n) / 2) =
      Real.exp (-t / 2) := by
    unfold CCM.nativeIntegerCoefficient
    rw [hroot, one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  unfold reversedLogUnitary classicalRho OPICAFollowup.sawtoothWeight
  have hce : (CCM.nativeIntegerCoefficient n : ℂ) *
      (Real.exp (-(t - Real.log n) / 2) : ℂ) = (Real.exp (-t / 2) : ℂ) := by exact_mod_cast he
  rw [harg]
  simp only [Complex.ofReal_mul]
  rw [← mul_assoc, hce]

theorem classicalChi_memLp : MemLp classicalChi 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hM : MemLp (reversedLogUnitary classicalChi) 2 volume :=
    MemLp.ae_eq reversedLogUnitary_classicalChi.symm causalInnerKernel_memLp
  apply (memLp_two_iff_integrable_sq_norm classicalChi_measurable.aestronglyMeasurable).mpr
  exact (reversedLogUnitary_integrable_norm_sq_iff classicalChi).mp
    ((memLp_two_iff_integrable_sq_norm hM.1).mp hM)

theorem classicalRho_memLp {n : ℕ} (hn : n ≠ 0) :
    MemLp (classicalRho n) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hshift := OPICAFollowup.memLp_two_sawtoothWeight.comp_measurePreserving
    (measurePreserving_sub_right volume (Real.log n))
  have hright : MemLp (fun t : ℝ => (CCM.nativeIntegerCoefficient n : ℂ) *
      OPICAFollowup.sawtoothWeight (t - Real.log n)) 2 volume := by
    simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul] using!
      hshift.const_smul (CCM.nativeIntegerCoefficient n : ℂ)
  have hM : MemLp (reversedLogUnitary (classicalRho n)) 2 volume :=
    MemLp.ae_eq (Filter.Eventually.of_forall fun t => (reversedLogUnitary_classicalRho hn t).symm) hright
  apply (memLp_two_iff_integrable_sq_norm (classicalRho_measurable n).aestronglyMeasurable).mpr
  exact (reversedLogUnitary_integrable_norm_sq_iff (classicalRho n)).mp
    ((memLp_two_iff_integrable_sq_norm hM.1).mp hM)


/-- The negative-time sawtooth component is explicitly cancelled by the
causal all-pass convolution, before any causal restriction is taken. -/
theorem fullCausalInnerPhysical_sawtooth_of_neg {t : ℝ} (ht : t < 0) :
    fullCausalInnerPhysical OPICAFollowup.sawtoothWeight t = 0 := by
  have hp : (fun s : ℝ => (causalInnerKernel s : ℂ) *
      OPICAFollowup.sawtoothWeight (t - s)) = (Ici (0 : ℝ)).indicator
        (fun s : ℝ => (Real.exp (t / 2) : ℂ) * Complex.exp (-(s : ℂ))) := by
    ext s
    by_cases hs : 0 ≤ s
    · rw [indicator_of_mem (show s ∈ Ici (0 : ℝ) from hs)]
      rw [OPICAFollowup.sawtoothWeight_of_neg (by linarith : t - s < 0)]
      simp only [causalInnerKernel, if_pos hs]
      have he : Real.exp (-s / 2) * Real.exp ((t - s) / 2) =
          Real.exp (t / 2) * Real.exp (-s) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      simpa only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
        using congrArg Complex.ofReal he
    · rw [indicator_of_notMem (show s ∉ Ici (0 : ℝ) from hs)]
      simp [causalInnerKernel, hs]
  have hi : (∫ s : ℝ in Ioi 0, Complex.exp (-(s : ℂ))) = 1 := by
    simpa using complex_power_exp_integral 0 (1 : ℂ) (by norm_num)
  unfold fullCausalInnerPhysical
  rw [OPICAFollowup.sawtoothWeight_of_neg ht, hp,
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul, hi]
  simp


def classicalChiL2 : PositiveProbeL2 := classicalChi_memLp.toLp classicalChi

def classicalRhoL2 (n : ℕ) (hn : n ≠ 0) : PositiveProbeL2 :=
  (classicalRho_memLp hn).toLp (classicalRho n)

def classicalSawtoothL2 : ProbeL2 :=
  OPICAFollowup.memLp_two_sawtoothWeight.toLp OPICAFollowup.sawtoothWeight

def comparisonE0 : ProbeL2 :=
  causalInnerKernel_memLp.toLp (fun t : ℝ => (causalInnerKernel t : ℂ))

theorem classicalSawtoothL2_coeFn : classicalSawtoothL2 =ᵐ[volume] OPICAFollowup.sawtoothWeight :=
  OPICAFollowup.memLp_two_sawtoothWeight.coeFn_toLp

theorem comparisonE0_coeFn : comparisonE0 =ᵐ[volume] fun t : ℝ => (causalInnerKernel t : ℂ) :=
  causalInnerKernel_memLp.coeFn_toLp

theorem reversedLogL2_classicalChi : reversedLogL2 classicalChiL2 = comparisonE0 := by
  apply Lp.ext
  exact (reversedLogL2Value_coeFn classicalChiL2).trans
    ((reversedLogUnitary_congr_ae classicalChi_memLp.coeFn_toLp).trans
      (reversedLogUnitary_classicalChi.trans comparisonE0_coeFn.symm))

theorem reversedLogL2_classicalRho {n : ℕ} (hn : n ≠ 0) :
    reversedLogL2 (classicalRhoL2 n hn) = (CCM.nativeIntegerCoefficient n : ℂ) •
      CCM.nativeCompletionL2Delay (Real.log n) classicalSawtoothL2 := by
  apply Lp.ext
  have hm := (reversedLogL2Value_coeFn (classicalRhoL2 n hn)).trans
    (reversedLogUnitary_congr_ae (classicalRho_memLp hn).coeFn_toLp)
  have hs := (measurePreserving_sub_right volume (Real.log n)).quasiMeasurePreserving.ae_eq
    classicalSawtoothL2_coeFn
  filter_upwards [hm, hs,
    CCM.nativeCompletionL2Delay_coeFn (Real.log n) classicalSawtoothL2,
    Lp.coeFn_smul (CCM.nativeIntegerCoefficient n : ℂ)
      (CCM.nativeCompletionL2Delay (Real.log n) classicalSawtoothL2)] with t ht hs hd hc
  dsimp only [Function.comp_def] at hs
  change reversedLogL2Value (classicalRhoL2 n hn) t = _
  rw [ht, hc, Pi.smul_apply, hd, hs, reversedLogUnitary_classicalRho hn]
  rfl

theorem fullCausalInnerOperator_delay (s : ℝ) (f : ProbeL2) :
    fullCausalInnerOperator (CCM.nativeCompletionL2Delay s f) =
      CCM.nativeCompletionL2Delay s (fullCausalInnerOperator f) := by
  have hk : kernelL2Operator causalInnerKernel causalInnerKernel_integrable
      (CCM.nativeCompletionL2Delay s f) = CCM.nativeCompletionL2Delay s
        (kernelL2Operator causalInnerKernel causalInnerKernel_integrable f) := by
    rw [kernelL2Operator_apply, kernelL2Operator_apply,
      ← (CCM.nativeCompletionL2Delay s).integral_comp_comm]
    apply integral_congr_ae
    filter_upwards with t
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    rw [probeL2Delay_comm]
  change CCM.nativeCompletionL2Delay s f - _ = CCM.nativeCompletionL2Delay s (f - _)
  rw [map_sub]
  exact congrArg (fun y : ProbeL2 => CCM.nativeCompletionL2Delay s f - y) hk

theorem fullCausalInnerOperator_indicator :
    fullCausalInnerOperator comparisonE0 = (comparisonU0 : ProbeL2) := by
  have hae := fullCausalInnerOperator_coeFn_of_representative comparisonE0
    (fun t : ℝ => (causalInnerKernel t : ℂ)) comparisonE0_coeFn
  have hleft2 : MemLp (fullCausalInnerPhysical (fun t : ℝ => (causalInnerKernel t : ℂ)))
      2 volume := (Lp.memLp (fullCausalInnerOperator comparisonE0)).ae_eq hae
  have hphys := probeL1L2Fourier_ext
    (fullCausalInnerPhysical (fun t : ℝ => (causalInnerKernel t : ℂ)))
    (fun t : ℝ => (classicalProbeKernel t : ℂ))
    (fullCausalInnerPhysical_integrable causalInnerKernel_integrable.ofReal)
    classicalProbeKernel_integrable.ofReal hleft2 classicalProbeKernel_memLp (by
      intro tau
      rw [fullCausalInnerPhysical_logFourier
          (f := fun t : ℝ => (causalInnerKernel t : ℂ)) causalInnerKernel_integrable.ofReal tau,
        causalInnerKernel_logFourier, classicalProbeKernel_logFourier]
      unfold causalInnerMultiplier classicalProbeMultiplier
      have hd : (tau : ℂ) * Complex.I + 1 / 2 ≠ 0 := by
        intro h
        have h := congrArg Complex.re h
        norm_num at h
      field_simp [hd]
      <;> ring)
  apply Lp.ext
  exact hae.trans (hphys.trans comparisonU0_coeFn.symm)

theorem fullCausalInnerOperator_sawtooth :
    fullCausalInnerOperator classicalSawtoothL2 = -(comparisonH0 : ProbeL2) := by
  have hae := fullCausalInnerOperator_coeFn_of_representative classicalSawtoothL2
    OPICAFollowup.sawtoothWeight classicalSawtoothL2_coeFn
  have hleft2 : MemLp (fullCausalInnerPhysical OPICAFollowup.sawtoothWeight) 2 volume :=
    (Lp.memLp (fullCausalInnerOperator classicalSawtoothL2)).ae_eq hae
  have hphys := probeL1L2Fourier_ext
    (fullCausalInnerPhysical OPICAFollowup.sawtoothWeight)
    (fun t : ℝ => -(classicalCompletionKernel t : ℂ))
    (fullCausalInnerPhysical_integrable OPICAFollowup.integrable_sawtoothWeight)
    classicalCompletionKernel_integrable.ofReal.neg hleft2 classicalCompletionKernel_memLp.neg (by
      intro tau
      rw [fullCausalInnerPhysical_logFourier OPICAFollowup.integrable_sawtoothWeight,
        OPICAFollowup.logFourier_sawtoothWeight]
      have hn : OPICAFollowup.logFourier (fun t : ℝ => -(classicalCompletionKernel t : ℂ)) tau =
          -OPICAFollowup.logFourier (fun t : ℝ => (classicalCompletionKernel t : ℂ)) tau := by
        unfold OPICAFollowup.logFourier
        simp_rw [mul_neg]
        exact integral_neg _
      rw [hn, classicalCompletionKernel_logFourier]
      unfold causalInnerMultiplier classicalProbeMultiplier
      rw [show (1 / 2 : ℂ) + (tau : ℂ) * Complex.I =
        (tau : ℂ) * Complex.I + 1 / 2 by ring]
      have hd : (tau : ℂ) * Complex.I + 1 / 2 ≠ 0 := by
        intro h
        have h := congrArg Complex.re h
        norm_num at h
      field_simp [hd]
      <;> ring)
  apply Lp.ext
  filter_upwards [hae.trans hphys, comparisonH0_coeFn, Lp.coeFn_neg (comparisonH0 : ProbeL2)]
    with t ht hh hn
  rw [ht, hn]
  change -(classicalCompletionKernel t : ℂ) = -(comparisonH0 : ProbeL2) t
  rw [hh]

theorem inner_reversedLog_classicalChi :
    fullCausalInnerOperator (reversedLogL2 classicalChiL2) = (comparisonU0 : ProbeL2) := by
  rw [reversedLogL2_classicalChi, fullCausalInnerOperator_indicator]

theorem inner_reversedLog_classicalRho {n : ℕ} (hn : n ≠ 0) :
    fullCausalInnerOperator (reversedLogL2 (classicalRhoL2 n hn)) =
      -(CCM.nativeIntegerCoefficient n : ℂ) •
        CCM.nativeCompletionL2Delay (Real.log n) (comparisonH0 : ProbeL2) := by
  rw [reversedLogL2_classicalRho hn, map_smul, fullCausalInnerOperator_delay,
    fullCausalInnerOperator_sawtooth, map_neg]
  simp


def classicalResidualL2 {N : ℕ} (x : Fin N → ℂ) : PositiveProbeL2 :=
  classicalChiL2 + ∑ i : Fin N, x i • classicalRhoL2 (i.val + 1) (by omega)

theorem classicalResidualL2_coeFn {N : ℕ} (x : Fin N → ℂ) :
    classicalResidualL2 x =ᵐ[volume.restrict (Ioi (0 : ℝ))] classicalFiniteResidual x := by
  have hterms : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin N,
      (x i • classicalRhoL2 (i.val + 1) (by omega) : PositiveProbeL2) t =
        x i * classicalRho (i.val + 1) t := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (x i) (classicalRhoL2 (i.val + 1) (by omega)),
      (classicalRho_memLp (by omega : i.val + 1 ≠ 0)).coeFn_toLp] with t hs hr
    change classicalRhoL2 (i.val + 1) (by omega) t = classicalRho (i.val + 1) t at hr
    rw [hs, Pi.smul_apply, hr]
    rfl
  filter_upwards [Lp.coeFn_add classicalChiL2
      (∑ i : Fin N, x i • classicalRhoL2 (i.val + 1) (by omega)),
    classicalChi_memLp.coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ
      (fun i : Fin N => x i • classicalRhoL2 (i.val + 1) (by omega)), hterms]
    with t ha hc hs ht
  change (classicalChiL2 + ∑ i : Fin N, x i • classicalRhoL2 (i.val + 1) (by omega)) t = _
  rw [ha]
  change classicalChiL2 t + (∑ i : Fin N, x i • classicalRhoL2 (i.val + 1) (by omega)) t = _
  change classicalChiL2 t = classicalChi t at hc
  rw [hc, hs]
  unfold classicalFiniteResidual
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ht i)

theorem comparisonRawFiniteResidual_eq_inner_M {N : ℕ} (x : Fin N → ℂ) :
    (comparisonRawFiniteResidual x : ProbeL2) =
      fullCausalInnerOperator (reversedLogL2 (classicalResidualL2 x)) := by
  unfold classicalResidualL2
  simp only [map_add, map_sum, map_smul, inner_reversedLog_classicalChi,
    inner_reversedLog_classicalRho]
  unfold comparisonRawFiniteResidual
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_neg,
    Submodule.coe_sum, Submodule.coe_smul_of_tower,
    probeDelay_coe_apply, neg_smul, smul_neg, ← Finset.sum_neg_distrib, sub_eq_add_neg]

theorem comparisonRawFiniteResidual_norm_eq_classical {N : ℕ} (x : Fin N → ℂ) :
    ‖comparisonRawFiniteResidual x‖ = ‖classicalResidualL2 x‖ := by
  change ‖(comparisonRawFiniteResidual x : ProbeL2)‖ = _
  rw [comparisonRawFiniteResidual_eq_inner_M, fullCausalInnerOperator_norm,
    reversedLogL2.norm_map]

theorem classicalResidualL2_norm_sq {N : ℕ} (x : Fin N → ℂ) :
    ‖classicalResidualL2 x‖ ^ 2 =
      ∫ u : ℝ in Ioi 0, ‖classicalFiniteResidual x u‖ ^ 2 := by
  have he : ‖classicalResidualL2 x‖ ^ 2 =
      ∫ u : ℝ in Ioi 0, ‖classicalResidualL2 x u‖ ^ 2 := by
    have h1 : (‖classicalResidualL2 x‖ ^ 2 : ℂ) =
        inner ℂ (classicalResidualL2 x) (classicalResidualL2 x) :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (classicalResidualL2 x)).symm
    rw [L2.inner_def] at h1
    have h2 : (∫ u : ℝ in Ioi 0, inner ℂ (classicalResidualL2 x u) (classicalResidualL2 x u)) =
        ((∫ u : ℝ in Ioi 0, ‖classicalResidualL2 x u‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      ext u
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [h2] at h1
    exact_mod_cast h1
  rw [he]
  exact integral_congr_ae ((classicalResidualL2_coeFn x).mono fun _ ht => by dsimp only; rw [ht])

/-- The native fixed-filter upper is transported from the actual unsmoothed
classical residual through the unitary and the literal probability contraction. -/
theorem filtered_probe_classical_comparison {N : ℕ} (x : Fin N → ℂ) :
    ‖fixedFilteredProbeResidual x‖ ^ 2 ≤
      ∫ u : ℝ in Ioi 0, ‖classicalFiniteResidual x u‖ ^ 2 := by
  rw [← classicalResidualL2_norm_sq]
  have h := (fixedFilteredProbeResidual_norm_le_raw x).trans_eq
    (comparisonRawFiniteResidual_norm_eq_classical x)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end Zeta23.OPICARound2
