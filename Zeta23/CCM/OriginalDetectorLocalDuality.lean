import Zeta23.CCM.PoleNeutralCompactH2SourceCongruence
import Zeta23.CCM.NativeWeilResponse
import Zeta23.CCM.OriginalSincNativeConvolution

/-!
# True local P-duality without global square-integrability of the prime field

This is the interval version of the compact weak-H2 transpose argument.
Unlike the compact-test variant, its smooth observation F need NOT be
compactly supported or globally L2. The five interval-integrability
premises are ordinary local analytic conditions, not an assumption that
the desired duality/equality holds. The next original-source adapter
must discharge them on each of four translated native prime histories.

Both endpoint contributions are paid by the ACTUAL compact inverse's
clamped value and first derivative, not thrown away by convention.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

theorem NativeCompactPoleH2.localP_duality
    {s : ℝ} {f F : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f)
    (hF : ContDiff ℝ 2 F)
    (h0 : IntervalIntegrable
      (fun x : ℝ => ((1 / 4 : ℂ) * u.value x + f x) * F x)
      volume (-s) s)
    (h1 : IntervalIntegrable
      (fun x : ℝ => u.first x * deriv F x)
      volume (-s) s)
    (h2 : IntervalIntegrable
      (fun x : ℝ => u.value x * deriv (deriv F) x)
      volume (-s) s)
    (hu : IntervalIntegrable
      (fun x : ℝ => u.value x * F x)
      volume (-s) s)
    (hf : IntervalIntegrable
      (fun x : ℝ => f x * F x)
      volume (-s) s) :
    (∫ x in (-s)..s, f x * F x) =
      ∫ x in (-s)..s, u.value x *
        (deriv (deriv F) x - (1 / 4 : ℂ) * F x) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFd : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hACfirst : AbsolutelyContinuousOnInterval
      (fun x : ℝ => u.first x * F x) (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      u.first_ac.smul hF.contDiffOn.absolutelyContinuousOnInterval
  have hACsecond : AbsolutelyContinuousOnInterval
      (fun x : ℝ => u.value x * deriv F x) (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      u.value_ac.smul hFd.contDiffOn.absolutelyContinuousOnInterval
  have hAEfirst :
      ∀ᵐ x : ℝ, x ∈ uIcc (-s) s →
        HasDerivAt (fun x : ℝ => u.first x * F x)
          (((1 / 4 : ℂ) * u.value x + f x) * F x +
            u.first x * deriv F x) x := by
    filter_upwards [u.first_derivative] with x hx _
    exact hx.mul ((hF.differentiable (by norm_num) x).hasDerivAt)
  have hAEsecond :
      ∀ᵐ x : ℝ, x ∈ uIcc (-s) s →
        HasDerivAt (fun x : ℝ => u.value x * deriv F x)
          (u.first x * deriv F x +
            u.value x * deriv (deriv F) x) x := by
    filter_upwards [u.value_derivative] with x hx _
    exact hx.mul ((hFd.differentiable (by norm_num) x).hasDerivAt)
  have hFTCfirst := complex_integral_eq_sub_of_ac_ae hACfirst
    (h0.add h1) hAEfirst
  have hFTCsecond := complex_integral_eq_sub_of_ac_ae hACsecond
    (h1.add h2) hAEsecond
  simp only [u.first_clamped.1, u.first_clamped.2, zero_mul, sub_self] at hFTCfirst
  simp only [u.value_clamped.1, u.value_clamped.2, zero_mul, sub_self] at hFTCsecond
  have hSumFirst :
      (∫ x in (-s)..s, ((1 / 4 : ℂ) * u.value x + f x) * F x) +
        (∫ x in (-s)..s, u.first x * deriv F x) = 0 := by
    simpa only [intervalIntegral.integral_add h0 h1] using hFTCfirst
  have hSumSecond :
      (∫ x in (-s)..s, u.first x * deriv F x) +
        (∫ x in (-s)..s, u.value x * deriv (deriv F) x) = 0 := by
    simpa only [intervalIntegral.integral_add h1 h2] using hFTCsecond
  have hTransfer :
      (∫ x in (-s)..s, ((1 / 4 : ℂ) * u.value x + f x) * F x) =
        (∫ x in (-s)..s, u.value x * deriv (deriv F) x) := by
    linear_combination hSumFirst - hSumSecond
  have hExpand :
      (∫ x in (-s)..s, ((1 / 4 : ℂ) * u.value x + f x) * F x) =
        (1 / 4 : ℂ) * (∫ x in (-s)..s, u.value x * F x) +
          (∫ x in (-s)..s, f x * F x) := by
    have heq :
        (fun x : ℝ => ((1 / 4 : ℂ) * u.value x + f x) * F x) =
        (fun x : ℝ => (1 / 4 : ℂ) * (u.value x * F x) + f x * F x) := by
      funext x
      ring
    rw [heq, intervalIntegral.integral_add (hu.const_mul _) hf,
      intervalIntegral.integral_const_mul]
  have hTarget :
      (∫ x in (-s)..s, u.value x *
        (deriv (deriv F) x - (1 / 4 : ℂ) * F x)) =
        (∫ x in (-s)..s, u.value x * deriv (deriv F) x) -
          (1 / 4 : ℂ) * (∫ x in (-s)..s, u.value x * F x) := by
    have heq :
        (fun x : ℝ => u.value x *
          (deriv (deriv F) x - (1 / 4 : ℂ) * F x)) =
        (fun x : ℝ => u.value x * deriv (deriv F) x -
          (1 / 4 : ℂ) * (u.value x * F x)) := by
      funext x
      ring
    rw [heq, intervalIntegral.integral_sub h2 (hu.const_mul _),
      intervalIntegral.integral_const_mul]
  calc
    (∫ x in (-s)..s, f x * F x) =
        (∫ x in (-s)..s, ((1 / 4 : ℂ) * u.value x + f x) * F x) -
          (1 / 4 : ℂ) * (∫ x in (-s)..s, u.value x * F x) := by
      rw [hExpand]
      ring
    _ = (∫ x in (-s)..s, u.value x * deriv (deriv F) x) -
          (1 / 4 : ℂ) * (∫ x in (-s)..s, u.value x * F x) := by
      rw [hTransfer]
    _ = ∫ x in (-s)..s, u.value x *
        (deriv (deriv F) x - (1 / 4 : ℂ) * F x) := hTarget.symm


/-- Literal source-specific local duality, not an arbitrary surrogate
prime field. The interval-integrability conditions are local and do
not impose global X in L2. Translating/reflection of the four histories
is a separate source-specific follow-up. -/
theorem NativeCompactPoleH2.originalKernelPrimeField_localPairing
    {s : ℝ} {f : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f)
    (h0 : IntervalIntegrable
      (fun x : ℝ => ((1 / 4 : ℂ) * u.value x + f x) *
        nativeOriginalKernelPrimeField x) volume (-s) s)
    (h1 : IntervalIntegrable
      (fun x : ℝ => u.first x * deriv nativeOriginalKernelPrimeField x)
      volume (-s) s)
    (h2 : IntervalIntegrable
      (fun x : ℝ => u.value x *
        deriv (deriv nativeOriginalKernelPrimeField) x)
      volume (-s) s)
    (hu : IntervalIntegrable
      (fun x : ℝ => u.value x * nativeOriginalKernelPrimeField x)
      volume (-s) s)
    (hf : IntervalIntegrable
      (fun x : ℝ => f x * nativeOriginalKernelPrimeField x)
      volume (-s) s) :
    (∫ x in (-s)..s, f x * nativeOriginalKernelPrimeField x) =
      ∫ x in (-s)..s, u.value x * (nativeOriginalPrimeField x : ℂ) := by
  have hF : ContDiff ℝ 2 nativeOriginalKernelPrimeField :=
    nativeOriginalKernelPrimeField_contDiff.of_le (by norm_num)
  have hLocal := u.localP_duality hF h0 h1 h2 hu hf
  rw [hLocal]
  apply intervalIntegral.integral_congr
  intro x _
  have hP := congrFun nativeOriginalKernelPrimeField_poleImage x
  change deriv (deriv nativeOriginalKernelPrimeField) x -
    (1 / 4 : ℂ) * nativeOriginalKernelPrimeField x =
    (nativeOriginalPrimeField x : ℂ) at hP
  rw [hP]

end Zeta23.CCM

#print axioms Zeta23.CCM.NativeCompactPoleH2.localP_duality

#print axioms Zeta23.CCM.NativeCompactPoleH2.originalKernelPrimeField_localPairing
