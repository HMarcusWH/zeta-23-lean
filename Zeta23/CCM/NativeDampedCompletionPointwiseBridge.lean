import Zeta23.CCM.NativeCausalKernelLaplaceDerivatives
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual strong L2 completion has the literal x-s convolution representative

The kernel's independent L2 membership pays pointwise integrability. On
every finite-measure observation set, 2ab <= a²+b² pays product integrability.
Finite-set indicator pairings commute with the actual Bochner integral.
Local integral uniqueness then identifies its actual L2 representative.
No prime-field L2 or range hypothesis is used in this bridge.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology ENNReal

namespace Zeta23.CCM

private theorem l2_norm_sq_integrable (f : NativeCompletionL2) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

private theorem kernel_norm_sq_integrable (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    Integrable (fun s : ℝ => ‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm
    (nativeDampedCompletionKernel_measurable epsilon).complex_ofReal.aestronglyMeasurable).mp
      (nativeDampedCompletionKernel_complex_memLp_two hepsilon)

private theorem shifted_l2_norm_sq_integrable (f : NativeCompletionL2) (x : ℝ) :
    Integrable (fun s : ℝ => ‖f (x - s)‖ ^ 2) :=
  (integrable_comp_sub_left (fun y : ℝ => ‖f y‖ ^ 2) x).mpr (l2_norm_sq_integrable f)

theorem nativeDampedCompletionPointwise_integrable (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (f : NativeCompletionL2) (x : ℝ) :
    Integrable (fun s : ℝ => (nativeDampedCompletionKernel epsilon s : ℂ) * f (x - s)) := by
  have hm : StronglyMeasurable (fun s : ℝ =>
      (nativeDampedCompletionKernel epsilon s : ℂ) * f (x - s)) :=
    (nativeDampedCompletionKernel_measurable epsilon).complex_ofReal.stronglyMeasurable.mul
      ((Lp.stronglyMeasurable f).comp_measurable (measurable_const.sub measurable_id))
  apply (((kernel_norm_sq_integrable epsilon hepsilon).add
    (shifted_l2_norm_sq_integrable f x)).div_const 2).mono' hm.aestronglyMeasurable
  filter_upwards with s
  change ‖(nativeDampedCompletionKernel epsilon s : ℂ) * f (x - s)‖ ≤
    (‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ ^ 2 + ‖f (x - s)‖ ^ 2) / 2
  rw [norm_mul]
  nlinarith [sq_nonneg (‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ - ‖f (x - s)‖)]

private theorem pointwise_integral_norm_le (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (f : NativeCompletionL2) (x : ℝ) :
    (∫ s : ℝ, ‖(nativeDampedCompletionKernel epsilon s : ℂ) * f (x - s)‖) ≤
      ((∫ s : ℝ, ‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ ^ 2) +
        ∫ y : ℝ, ‖f y‖ ^ 2) / 2 := by
  have hker := kernel_norm_sq_integrable epsilon hepsilon
  have hf := shifted_l2_norm_sq_integrable f x
  calc
    _ ≤ ∫ s : ℝ, (‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ ^ 2 +
        ‖f (x - s)‖ ^ 2) / 2 := by
      apply integral_mono (nativeDampedCompletionPointwise_integrable epsilon hepsilon f x).norm
        ((hker.add hf).div_const 2)
      intro s
      change ‖(nativeDampedCompletionKernel epsilon s : ℂ) * f (x - s)‖ ≤
        (‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ ^ 2 + ‖f (x - s)‖ ^ 2) / 2
      rw [norm_mul]
      nlinarith [sq_nonneg (‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ - ‖f (x - s)‖)]
    _ = _ := by
      rw [integral_div, integral_add hker hf,
        integral_sub_left_eq_self (fun y : ℝ => ‖f y‖ ^ 2) volume x]

theorem nativeDampedCompletionPointwise_integrable_prod_on_finite_set
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (f : NativeCompletionL2)
    (S : Set ℝ) (hS : volume S < ∞) :
    Integrable (fun p : ℝ × ℝ =>
      (nativeDampedCompletionKernel epsilon p.2 : ℂ) * f (p.1 - p.2))
      ((volume.restrict S).prod volume) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    (nativeDampedCompletionKernel epsilon p.2 : ℂ) * f (p.1 - p.2)
  have hk : Measurable (fun p : ℝ × ℝ => (nativeDampedCompletionKernel epsilon p.2 : ℂ)) :=
    (nativeDampedCompletionKernel_measurable epsilon).complex_ofReal.comp measurable_snd
  have hfmeas : StronglyMeasurable (fun p : ℝ × ℝ => f (p.1 - p.2)) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_fst.sub measurable_snd)
  have hm : StronglyMeasurable F := hk.stronglyMeasurable.mul hfmeas
  have hmae : AEStronglyMeasurable F ((volume.restrict S).prod volume) := hm.aestronglyMeasurable
  apply (integrable_prod_iff hmae).mpr
  constructor
  · exact Filter.Eventually.of_forall
      (nativeDampedCompletionPointwise_integrable epsilon hepsilon f)
  · let C : ℝ := ((∫ s : ℝ, ‖(nativeDampedCompletionKernel epsilon s : ℂ)‖ ^ 2) +
      ∫ y : ℝ, ‖f y‖ ^ 2) / 2
    have hinnermeas : AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, ‖F (x, y)‖)
        (volume.restrict S) := hmae.norm.integral_prod_right'
    apply (integrableOn_const (μ := volume) (s := S) (C := C) hS.ne).mono' hinnermeas
    filter_upwards with x
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact pointwise_integral_norm_le epsilon hepsilon f x

private theorem integrand_inner_indicator (epsilon : ℝ) (f : NativeCompletionL2)
    (S : Set ℝ) (hS : MeasurableSet S) (hfinite : volume S ≠ ∞) (s : ℝ) :
    inner ℂ (indicatorConstLp 2 hS hfinite (1 : ℂ))
        (nativeDampedCompletionL2Integrand epsilon f s) =
      ∫ x : ℝ in S, (nativeDampedCompletionKernel epsilon s : ℂ) * f (x - s) := by
  rw [L2.inner_indicatorConstLp_one]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (Lp.coeFn_smul (nativeDampedCompletionKernel epsilon s) (nativeCompletionL2Delay s f)),
    ae_restrict_of_ae (nativeCompletionL2Delay_coeFn s f)] with x hx hd
  change (nativeDampedCompletionKernel epsilon s • nativeCompletionL2Delay s f) x = _
  rw [hx, Pi.smul_apply, hd, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul,
    RCLike.ofReal_eq_complex_ofReal]

theorem nativeDampedCompletionL2Operator_setIntegral_pointwise
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (f : NativeCompletionL2)
    (S : Set ℝ) (hS : MeasurableSet S) (hfinite : volume S < ∞) :
    (∫ x : ℝ in S, nativeDampedCompletionL2Operator epsilon hepsilon f x) =
      ∫ x : ℝ in S, nativeDampedCompletionPointwise epsilon f x := by
  rw [← L2.inner_indicatorConstLp_one hS hfinite.ne,
    nativeDampedCompletionL2Operator_apply]
  change inner ℂ (indicatorConstLp 2 hS hfinite.ne (1 : ℂ))
      (∫ s : ℝ, nativeDampedCompletionL2Integrand epsilon f s) = _
  rw [← integral_inner (𝕜 := ℂ)
    (nativeDampedCompletionL2Integrand_integrable hepsilon f)]
  simp_rw [integrand_inner_indicator epsilon f S hS hfinite.ne]
  exact (integral_integral_swap
    (nativeDampedCompletionPointwise_integrable_prod_on_finite_set
      epsilon hepsilon f S hfinite)).symm

/-- The actual full-line strong L2 operator has the literal convolution
representative almost everywhere. The input is an arbitrary L2 class. -/
theorem nativeDampedCompletionL2Operator_coeFn_pointwise
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (f : NativeCompletionL2) :
    nativeDampedCompletionL2Operator epsilon hepsilon f =ᵐ[volume]
      nativeDampedCompletionPointwise epsilon f := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro S _ hS
    exact integrableOn_Lp_of_measure_ne_top
      (nativeDampedCompletionL2Operator epsilon hepsilon f) (by norm_num) hS.ne
  · intro S _ hS
    exact (nativeDampedCompletionPointwise_integrable_prod_on_finite_set
      epsilon hepsilon f S hS).integral_prod_left
  · exact nativeDampedCompletionL2Operator_setIntegral_pointwise epsilon hepsilon f

theorem nativeDampedCompletionPointwise_memLp
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (f : NativeCompletionL2) :
    MemLp (nativeDampedCompletionPointwise epsilon f) 2 volume :=
  MemLp.ae_eq (nativeDampedCompletionL2Operator_coeFn_pointwise epsilon hepsilon f)
    (Lp.memLp (nativeDampedCompletionL2Operator epsilon hepsilon f))

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDampedCompletionPointwise_integrable
#print axioms Zeta23.CCM.nativeDampedCompletionPointwise_integrable_prod_on_finite_set
#print axioms Zeta23.CCM.nativeDampedCompletionL2Operator_setIntegral_pointwise
#print axioms Zeta23.CCM.nativeDampedCompletionL2Operator_coeFn_pointwise
#print axioms Zeta23.CCM.nativeDampedCompletionPointwise_memLp
