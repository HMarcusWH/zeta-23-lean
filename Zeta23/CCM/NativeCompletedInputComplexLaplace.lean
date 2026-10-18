import Zeta23.CCM.NativeCompletionComplexLaplace

/-!
The literal completed input Y=c*U has the product of the actual complex
Laplace transforms. Integrability comes from the independently proved
causal L1 inputs. This does not assume X belongs to L2 or Y lies in a range.
The further identification of the drive multiplier with -zeta' J is separate.
-/

noncomputable section

open Set MeasureTheory
open scoped Convolution

namespace Zeta23.CCM

def nativeCausalComplexDamping (w : ℂ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-w * (t : ℂ)) * (f t : ℂ)

theorem nativeCausalComplexDamping_integrable {w : ℂ} (hw : 0 ≤ w.re)
    {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ t : ℝ, t < 0 → f t = 0) :
    Integrable (nativeCausalComplexDamping w f) := by
  have hexp : Continuous (fun t : ℝ => Complex.exp (-w * (t : ℂ))) := by fun_prop
  have hfc : Integrable (fun t : ℝ => (f t : ℂ)) := hf.ofReal
  have hm : AEStronglyMeasurable (nativeCausalComplexDamping w f) volume :=
    hexp.aestronglyMeasurable.mul hfc.aestronglyMeasurable
  apply hf.norm.mono' hm
  filter_upwards with t
  change ‖Complex.exp (-w * (t : ℂ)) * (f t : ℂ)‖ ≤ ‖f t‖
  by_cases ht : t < 0
  · simp [hf0 t ht]
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    have hre : (-w * (t : ℂ)).re = -w.re * t := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    rw [norm_mul, Complex.norm_exp, hre,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith))

theorem nativeCompletedInput_complexDamping_eq_convolution (w : ℂ) (t : ℝ) :
    nativeCausalComplexDamping w nativeCompletedInput t =
      ((nativeCausalComplexDamping w nativeCompletionCorrection) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (nativeCausalComplexDamping w nativeOriginalIntegerDrive)) t := by
  simp only [nativeCausalComplexDamping, nativeCompletedInput, convolution_def,
    ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [Complex.ofReal_mul]
  have hexp : Complex.exp (-w * (t : ℂ)) =
      Complex.exp (-w * (s : ℂ)) * Complex.exp (-w * ((t - s : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- The actual stable input's complex transform is the rational signed
correction multiplier times the transform of its unchanged integer drive. -/
theorem nativeCompletedInput_complexLaplace_eq_c_mul_drive {w : ℂ} (hw : 0 ≤ w.re) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeCompletedInput t : ℂ)) =
      nativeCompletionRationalMultiplier w *
        ∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeOriginalIntegerDrive t : ℂ) := by
  have hc := nativeCausalComplexDamping_integrable hw nativeCompletionCorrection_integrable
    (fun t ht => nativeCompletionCorrection_zero_of_neg ht)
  have hu := nativeCausalComplexDamping_integrable hw nativeOriginalIntegerDrive_integrable
    (fun t ht => nativeOriginalIntegerDrive_zero_of_neg ht)
  change (∫ t : ℝ, nativeCausalComplexDamping w nativeCompletedInput t) = _
  simp_rw [nativeCompletedInput_complexDamping_eq_convolution]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hc hu]
  change (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeCompletionCorrection t : ℂ)) *
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeOriginalIntegerDrive t : ℂ)) = _
  rw [nativeCompletionCorrection_complexLaplace (by linarith)]

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCausalComplexDamping_integrable
#print axioms Zeta23.CCM.nativeCompletedInput_complexDamping_eq_convolution
#print axioms Zeta23.CCM.nativeCompletedInput_complexLaplace_eq_c_mul_drive
