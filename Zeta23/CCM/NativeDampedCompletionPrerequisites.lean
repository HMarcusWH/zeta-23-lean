import Zeta23.CCM.NativePositiveCompletionCertificate
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Measure

/-!
# Actual damped completion kernel and causal delay prerequisites

This is the literal damped native floor kernel, with its complete L1 mass
bound. The L2 delay uses x-t, is isometric, and preserves causality for
nonnegative delays. These are prerequisites for the strong L2 integral
construction of the completion operator.

This file does not construct the completed operator on the closed causal
L2 subspace or its causal adjoint, and does not fill M19. Finite residual
identities, strong convergence, range membership, and vanishing terminal
projection remain OPEN. A full-line adjoint is not a causal adjoint.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

def nativeDampedCompletionKernel (epsilon t : ℝ) : ℝ :=
  Real.exp (-epsilon * t) * nativePositiveCompletion t

theorem nativeDampedCompletionKernel_nonneg (epsilon t : ℝ) :
    0 ≤ nativeDampedCompletionKernel epsilon t :=
  mul_nonneg (Real.exp_pos _).le (nativePositiveCompletion_nonneg t)

theorem nativeDampedCompletionKernel_zero_of_neg (epsilon : ℝ) {t : ℝ} (ht : t < 0) :
    nativeDampedCompletionKernel epsilon t = 0 := by
  rw [nativeDampedCompletionKernel, nativePositiveCompletion_eq_zero_of_neg ht, mul_zero]

theorem nativeDampedCompletionKernel_measurable (epsilon : ℝ) :
    Measurable (nativeDampedCompletionKernel epsilon) :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    nativePositiveCompletion_measurable

theorem nativeDampedCompletionKernel_le_native {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (t : ℝ) : nativeDampedCompletionKernel epsilon t ≤ nativePositiveCompletion t := by
  by_cases ht : 0 ≤ t
  · have hexp : Real.exp (-epsilon * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hepsilon) ht)
    exact (mul_le_mul_of_nonneg_right hexp (nativePositiveCompletion_nonneg t)).trans_eq
      (one_mul _)
  · rw [nativeDampedCompletionKernel_zero_of_neg epsilon (lt_of_not_ge ht),
      nativePositiveCompletion_eq_zero_of_neg (lt_of_not_ge ht)]

theorem nativeDampedCompletionKernel_integrable {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    Integrable (nativeDampedCompletionKernel epsilon) := by
  apply nativePositiveCompletion_integrable.mono'
    (nativeDampedCompletionKernel_measurable epsilon).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_of_nonneg (nativeDampedCompletionKernel_nonneg epsilon t)]
    exact nativeDampedCompletionKernel_le_native hepsilon t

theorem nativeDampedCompletionKernel_integral_norm_le_native {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    (∫ t : ℝ, ‖nativeDampedCompletionKernel epsilon t‖) ≤
      ∫ t : ℝ, ‖nativePositiveCompletion t‖ := by
  apply integral_mono (nativeDampedCompletionKernel_integrable hepsilon).norm
    nativePositiveCompletion_integrable.norm
  intro t
  change ‖nativeDampedCompletionKernel epsilon t‖ ≤ ‖nativePositiveCompletion t‖
  rw [Real.norm_of_nonneg (nativeDampedCompletionKernel_nonneg epsilon t),
    Real.norm_of_nonneg (nativePositiveCompletion_nonneg t)]
  exact nativeDampedCompletionKernel_le_native hepsilon t

theorem nativeDampedCompletionKernel_integral_norm_lt_605_div_621 {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    (∫ t : ℝ, ‖nativeDampedCompletionKernel epsilon t‖) < (605 / 621 : ℝ) :=
  (nativeDampedCompletionKernel_integral_norm_le_native hepsilon).trans_lt
    nativePositiveCompletion_integral_norm_lt_605_div_621

/-- Exact full-line delay, used only as a prerequisite for restriction to
the causal L2 subspace. Its direction is x-t, not x+t. -/
def nativeCompletionL2Delay (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x - t) (measurePreserving_sub_right volume t)

theorem nativeCompletionL2Delay_norm (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖nativeCompletionL2Delay t f‖ = ‖f‖ :=
  (nativeCompletionL2Delay t).norm_map f

theorem nativeCompletionL2Delay_coeFn (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    nativeCompletionL2Delay t f =ᵐ[volume] fun x : ℝ => f (x - t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume t)

/-- Causality is preserved at the equivalence-class level for every
nonnegative delay; no pointwise representative is assumed canonical. -/
theorem nativeCompletionL2Delay_causal {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : ∀ᵐ x : ℝ, x < 0 → f x = 0) :
    ∀ᵐ x : ℝ, x < 0 → nativeCompletionL2Delay t f x = 0 := by
  have hshift := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae hf
  filter_upwards [nativeCompletionL2Delay_coeFn t f, hshift] with x hx hfx
  intro hxneg
  rw [hx]
  exact hfx (by linarith)

/-- The literal pointwise convolution formula. This definition is not
promoted to a bounded causal L2 operator without its remaining domain proof. -/
def nativeDampedCompletionPointwise (epsilon : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, (nativeDampedCompletionKernel epsilon t : ℂ) * f (x - t)

theorem nativeDampedCompletionPointwise_causal (epsilon : ℝ) {f : ℝ → ℂ}
    (hf : ∀ x : ℝ, x < 0 → f x = 0) {x : ℝ} (hx : x < 0) :
    nativeDampedCompletionPointwise epsilon f x = 0 := by
  unfold nativeDampedCompletionPointwise
  have hzero : (fun t : ℝ => (nativeDampedCompletionKernel epsilon t : ℂ) * f (x - t)) = 0 := by
    funext t
    change _ = (0 : ℂ)
    by_cases ht : 0 ≤ t
    · rw [hf (x - t) (by linarith), mul_zero]
    · rw [nativeDampedCompletionKernel_zero_of_neg epsilon (lt_of_not_ge ht),
        Complex.ofReal_zero, zero_mul]
  rw [hzero]
  exact integral_zero ℝ ℂ

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDampedCompletionKernel_integrable
#print axioms Zeta23.CCM.nativeDampedCompletionKernel_integral_norm_lt_605_div_621
#print axioms Zeta23.CCM.nativeCompletionL2Delay_norm
#print axioms Zeta23.CCM.nativeCompletionL2Delay_causal
#print axioms Zeta23.CCM.nativeDampedCompletionPointwise_causal
