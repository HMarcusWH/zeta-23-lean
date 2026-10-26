import Zeta23.OPICARound2.CausalProbe

/-! Independent physical and causal-domain consumers for P01--P05.
These declarations retain the open range premise and test literal source identity,
the pointwise/equivalence-class bridge and the removable transform value. -/

noncomputable section

open Set MeasureTheory
open scoped Topology ENNReal BigOperators

namespace Zeta23.OPICARound2.Validation

theorem consumer_001 : probeSigma = (1 / 4096 : ℝ) := probeSigma_eq

theorem consumer_002 (t : ℝ) : jPlus t = CCM.nativeOriginalSource (t - probeSigma) := rfl

theorem consumer_003 {t : ℝ} (ht : t ∉ Icc 0 (2 * probeSigma)) : jPlus t = 0 :=
  jPlus_zero_outside ht

theorem consumer_004 : ContDiff ℝ (⊤ : ℕ∞) jPlus := jPlus_contDiff

theorem consumer_005 : Integrable jPlus := jPlus_integrable

theorem consumer_006 : MemLp (fun t : ℝ => (jPlus t : ℂ)) 2 volume := jPlus_memLp

theorem consumer_007 : (probeSource : CCM.NativeCompletionL2) =ᵐ[volume]
    fun t : ℝ => (CCM.nativeOriginalSource (t - probeSigma) : ℂ) := probeSource_coeFn

theorem consumer_008 : (∫ t : ℝ, jPlus t) = (1 / 16 : ℝ) := jPlus_integral

theorem consumer_009 (z : ℂ) : JPlus z = Complex.exp (-z * (probeSigma : ℂ)) *
    (((Complex.I * z) ^ 2 + 1 / 4) ^ 2 *
      CCM.UniversalSinc.product probeSigma (Complex.I * z)) := JPlus_one_copy_formula z

theorem consumer_010 : (∫ t : ℝ, Real.exp (t / 2) * jPlus t) = 0 ∧
    (∫ t : ℝ, Real.exp (-t / 2) * jPlus t) = 0 ∧
    (∫ t : ℝ, t * Real.exp (t / 2) * jPlus t) = 0 ∧
    (∫ t : ℝ, t * Real.exp (-t / 2) * jPlus t) = 0 := jPlus_double_killed_moments

theorem consumer_011 : probeC = CCM.nativeRationalCausalKernel := probeC_eq_nativeRationalKernel

theorem consumer_012 : probeOperator = CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) := rfl

theorem consumer_013 : (probeTarget : CCM.NativeCompletionL2) =ᵐ[volume]
    fun t : ℝ => ∫ s : ℝ,
      (CCM.nativeCompletionCorrection s : ℂ) *
        (CCM.nativeOriginalSource ((t - s) - probeSigma) : ℂ) := probeTarget_coeFn

theorem consumer_014 : (probeCompletedSource : CCM.NativeCompletionL2) =ᵐ[volume]
    fun t : ℝ => ∫ s : ℝ,
      (CCM.nativePositiveCompletion s : ℂ) *
        (CCM.nativeOriginalSource ((t - s) - probeSigma) : ℂ) := probeCompletedSource_coeFn

theorem consumer_015 : Integrable probeV ∧ Integrable probeW ∧
    MemLp probeV 2 volume ∧ MemLp probeW 2 volume :=
  ⟨probeV_integrable, probeW_integrable, probeV_memLp, probeW_memLp⟩

theorem consumer_016 {t : ℝ} (ht : t < 0) : probeV t = 0 ∧ probeW t = 0 :=
  ⟨probeV_zero_of_neg ht, probeW_zero_of_neg ht⟩

theorem consumer_017 (z : ℂ) (hz : 0 ≤ z.re) :
    probeLaplace probeV z = CCM.nativeCompletionRationalMultiplier z * JPlus z :=
  probeV_laplace hz

theorem consumer_018 (z : ℂ) (hz : 0 ≤ z.re) :
    probeLaplace probeW z = CCM.nativePositiveCompletionLaplace z * JPlus z :=
  probeW_laplace_actual hz

theorem consumer_019 (z : ℂ) (hz : 0 < z.re) (hne : z ≠ 1 / 2) :
    probeLaplace probeW z =
      CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2) * JPlus z :=
  probeW_laplace hz hne

/-- The actual A has value 1/2 at the removable point; the zero is supplied by J. -/
theorem consumer_020 : CCM.nativePositiveCompletionLaplace (1 / 2 : ℂ) = 1 / 2 ∧
    JPlus (1 / 2 : ℂ) = 0 ∧ probeLaplace probeW (1 / 2 : ℂ) = 0 :=
  ⟨CCM.nativePositiveCompletion_complexLaplace_half, JPlus_half, probeW_laplace_half⟩

theorem consumer_021 : (∫ t : ℝ, probeV t) = (-1 / 24 : ℂ) ∧ probeTarget ≠ 0 :=
  ⟨probeV_integral, probeTarget_ne_zero⟩

theorem consumer_022 (t : ℝ) : probeW t =
    ∑ n ∈ Finset.range (⌊Real.exp t⌋₊ + 1),
      (CCM.nativeIntegerCoefficient n : ℂ) * probeV (t - Real.log n) :=
  native_probe_integer_action t

theorem consumer_023 {n : ℕ} (hn : n ≠ 0) : probeColumn n =
    (CCM.nativeIntegerCoefficient n : ℂ) •
      probeDelay (Real.log n) (probe_log_nonneg hn) probeCompletedSource :=
  probeColumn_eq_delay hn

theorem consumer_024 {n : ℕ} (hn : n ≠ 0) :
    (probeInput n : CCM.NativeCompletionL2) =ᵐ[volume] fun t : ℝ =>
      (CCM.nativeIntegerCoefficient n : ℂ) *
        (CCM.nativeOriginalSource ((t - Real.log n) - probeSigma) : ℂ) :=
  probeInput_coeFn hn

theorem consumer_025 {n : ℕ} (hn : n ≠ 0) :
    (probeColumn n : CCM.NativeCompletionL2) =ᵐ[volume] fun t : ℝ =>
      (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n) :=
  probeColumn_coeFn hn

theorem consumer_026 {N : ℕ} (x : Fin N → ℂ) :
    probeFiniteOutput x = probeOperator (probeFiniteInput x) := probeFiniteOutput_eq_operator x

theorem consumer_027 (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    Real.sqrt (2 * z.re) *
      ‖CCM.nativeCausalLaplaceMoment z 0 (f : CCM.NativeCompletionL2)‖ ≤ ‖f‖ :=
  probe_laplace_evaluation_bound z hz f

/-- The arbitrary actual zero carries any of its possible finite multiplicities. -/
theorem consumer_028 (rho : zetaZeroConfig.carrier) (hright : 1 / 2 < (rho : ℂ).re)
    {g : CausalProbeL2} (hg : g ∈ closure (Set.range probeOperator)) :
    Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖probeTarget - g‖ :=
  probe_zero_separation_rangeClosure rho hright hg

theorem consumer_029 (rho : zetaZeroConfig.carrier) (hright : 1 / 2 < (rho : ℂ).re) :
    probeTarget ∉ closure (Set.range probeOperator) :=
  probeTarget_not_mem_rangeClosure rho hright

theorem consumer_030 (h : probeTarget ∈ closure (Set.range
    (CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl)))) : RiemannHypothesis :=
  rh_of_native_probe_range h

#print axioms Zeta23.OPICARound2.delayed_original_source
#print axioms Zeta23.OPICARound2.native_probe_transforms
#print axioms Zeta23.OPICARound2.native_probe_integer_action
#print axioms Zeta23.OPICARound2.native_probe_zero_separation
#print axioms Zeta23.OPICARound2.rh_of_native_probe_range

end Zeta23.OPICARound2.Validation
