import Zeta23.CCM.NativeIntegerKernelComplexLaplace
import Zeta23.CCM.NativeLaplaceHalfPlaneContinuation
import Zeta23.CCM.NativeCausalKernelLaplaceDerivatives

/-!
The actual floor-kernel multiplier is continued only where zeta is regular.
Its removable point w=1/2 is evaluated separately using the true residue,
never by substituting into the totalized product R(w)*zeta(w+1/2).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Zeta23.CCM

def nativePositiveCompletionLaplace (w : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativePositiveCompletion t : ℂ)

theorem nativePositiveCompletionLaplace_analyticAt {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ nativePositiveCompletionLaplace w := by
  have heq : (fun z : ℂ => nativeCompletionKernelLaplaceMoment 0 z 0) =
      nativePositiveCompletionLaplace := by
    funext z
    unfold nativePositiveCompletionLaplace nativeCompletionKernelLaplaceMoment nativeDampedCompletionKernel
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, pow_zero, mul_one]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [← heq]
  exact nativeCompletionKernelLaplace_analyticAt 0 (le_rfl) w hw

theorem nativeCompletionRationalMultiplier_analyticAt {w : ℂ} (hw : 0 ≤ w.re) :
    AnalyticAt ℂ nativeCompletionRationalMultiplier w := by
  have hd1 : w + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hd2 : w + 3 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  exact (analyticAt_id.sub analyticAt_const).div
    ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const))
    (mul_ne_zero hd1 hd2)

theorem nativePositiveCompletion_complexLaplace {w : ℂ} (hw : 0 < w.re)
    (hne : w ≠ 1 / 2) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativePositiveCompletion t : ℂ)) =
      nativeCompletionRationalMultiplier w * riemannZeta (w + 1 / 2) := by
  have ha : AnalyticOnNhd ℂ nativePositiveCompletionLaplace nativeLaplaceContinuationDomain :=
    fun _ hz => nativePositiveCompletionLaplace_analyticAt hz.1
  have hg : AnalyticOnNhd ℂ
      (fun z : ℂ => nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2))
      nativeLaplaceContinuationDomain := by
    intro z hz
    have hzeta : z + 1 / 2 ≠ 1 := by
      intro h
      apply hz.2
      linear_combination h
    have harg : AnalyticAt ℂ (fun y : ℂ => y + 1 / 2) z :=
      analyticAt_id.add analyticAt_const
    exact (nativeCompletionRationalMultiplier_analyticAt hz.1.le).mul
      (AnalyticAt.comp (f := fun y : ℂ => y + 1 / 2) (x := z)
        (analyticOn_riemannZeta (z + 1 / 2) hzeta) harg)
  exact nativeLaplace_eqOn_of_eqOn_rightHalfPlane ha hg
    (fun z hz => nativePositiveCompletion_complexLaplace_of_half_lt_re hz) ⟨hw, hne⟩

/-- The removable pole has actual value 1/2; the zero of R cancels the
pole of zeta with residue one rather than creating a zero at w=1/2. -/
theorem nativePositiveCompletion_complexLaplace_half :
    nativePositiveCompletionLaplace (1 / 2 : ℂ) = 1 / 2 := by
  have hshift : Tendsto (fun z : ℂ => z + 1 / 2) (𝓝[≠] (1 / 2 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto (fun z : ℂ => z + 1 / 2) (𝓝 (1 / 2 : ℂ)) (𝓝 (1 : ℂ)) := by
        have hc : Continuous (fun z : ℂ => z + 1 / 2) := continuous_id.add continuous_const
        convert hc.tendsto (1 / 2 : ℂ) using 1 <;> norm_num
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z ≠ (1 / 2 : ℂ) at hz
      change z + 1 / 2 ≠ (1 : ℂ)
      intro h
      apply hz
      linear_combination h
  have hden : Tendsto (fun z : ℂ => (z + 1 / 2) * (z + 3 / 2))
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (2 : ℂ)) := by
    have h : Continuous (fun z : ℂ => (z + 1 / 2) * (z + 3 / 2)) := by fun_prop
    convert h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
  have hr : Tendsto (fun z : ℂ => ((z + 1 / 2) - 1) * riemannZeta (z + 1 / 2) /
      ((z + 1 / 2) * (z + 3 / 2))) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (1 / 2 : ℂ)) :=
    (riemannZeta_residue_one.comp hshift).div hden (by norm_num)
  have hevent : nativePositiveCompletionLaplace =ᶠ[𝓝[≠] (1 / 2 : ℂ)]
      (fun z : ℂ => ((z + 1 / 2) - 1) * riemannZeta (z + 1 / 2) /
        ((z + 1 / 2) * (z + 3 / 2))) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re))] with z hz hpos
    change z ≠ (1 / 2 : ℂ) at hz
    change nativePositiveCompletionLaplace z = _
    rw [nativePositiveCompletionLaplace, nativePositiveCompletion_complexLaplace hpos hz,
      nativeCompletionRationalMultiplier]
    ring
  have hl := (nativePositiveCompletionLaplace_analyticAt
    (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (1 / 2 : ℂ) ≤ 𝓝 (1 / 2 : ℂ))
  exact tendsto_nhds_unique hl (hr.congr' hevent.symm)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePositiveCompletionLaplace_analyticAt
#print axioms Zeta23.CCM.nativePositiveCompletion_complexLaplace
#print axioms Zeta23.CCM.nativePositiveCompletion_complexLaplace_half
