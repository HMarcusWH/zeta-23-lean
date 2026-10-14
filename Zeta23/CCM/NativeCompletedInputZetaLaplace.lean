import Zeta23.CCM.NativeIntegerDriveComplexLaplace
import Zeta23.CCM.NativePositiveCompletionComplexLaplace
import Zeta23.CCM.NativeCausalLaplaceDerivatives

/-!
The actual unchanged integer drive and stable completed input have their
zeta-derivative multipliers on the regular positive half-plane. Continuation
uses their independently proved causal L2 membership. The exceptional point
is kept separate, and the source transform is the actual j=P²q transform.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Zeta23.CCM

def nativeOriginalIntegerDriveLaplace (w : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeOriginalIntegerDrive t : ℂ)

def nativeOriginalIntegerDriveCausalL2 : nativeCompletionCausalL2 :=
  ⟨nativeOriginalDampedIntegerDriveL2 0 (le_rfl),
    nativeOriginalDampedIntegerDriveL2_causal 0 (le_rfl)⟩

theorem nativeOriginalIntegerDriveLaplace_analyticAt {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ nativeOriginalIntegerDriveLaplace w := by
  have heq : (fun z : ℂ => nativeCausalLaplaceMoment z 0
      (nativeOriginalIntegerDriveCausalL2 : NativeCompletionL2)) = nativeOriginalIntegerDriveLaplace := by
    funext z
    unfold nativeCausalLaplaceMoment nativeOriginalIntegerDriveLaplace
    apply integral_congr_ae
    filter_upwards [nativeOriginalDampedIntegerDriveL2_coeFn 0 (le_rfl)] with t ht
    change (t : ℂ) ^ 0 * Complex.exp (-z * (t : ℂ)) *
      nativeOriginalDampedIntegerDriveL2 0 (le_rfl) t = _
    rw [ht]
    simp only [nativeOriginalDampedIntegerDrive, neg_zero, zero_mul,
      Real.exp_zero, one_mul, pow_zero]
  rw [← heq]
  exact nativeCausalLaplaceMoment_analyticAt w hw 0 nativeOriginalIntegerDriveCausalL2

theorem nativeOriginalSourceLaplace_analyticAt (w : ℂ) :
    AnalyticAt ℂ nativeOriginalSourceLaplace w := by
  have heq : nativeOriginalSourceLaplace = fun z : ℂ =>
      ((Complex.I * z) ^ 2 + 1 / 4) ^ 2 * UniversalSinc.product UniversalSinc.fixedScale (Complex.I * z) := by
    funext z
    exact Zeta23.ExceptionalZero.nativeOriginalSourceLaplace_formula z
  have hi : AnalyticAt ℂ (fun z : ℂ => Complex.I * z) w := analyticAt_const.mul analyticAt_id
  have hp : AnalyticAt ℂ (fun z : ℂ => ((Complex.I * z) ^ 2 + 1 / 4) ^ 2) w :=
    ((hi.pow 2).add analyticAt_const).pow 2
  have hq : AnalyticAt ℂ (fun z : ℂ => UniversalSinc.product UniversalSinc.fixedScale (Complex.I * z)) w :=
    AnalyticAt.comp (f := fun z : ℂ => Complex.I * z) (x := w)
      (UniversalSinc.analyticAt_product UniversalSinc.fixedScale_pos.le (Complex.I * w)) hi
  rw [heq]
  exact hp.mul hq

theorem nativeOriginalIntegerDrive_complexLaplace {w : ℂ} (hw : 0 < w.re)
    (hne : w ≠ 1 / 2) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeOriginalIntegerDrive t : ℂ)) =
      -deriv riemannZeta (w + 1 / 2) * nativeOriginalSourceLaplace w := by
  have ha : AnalyticOnNhd ℂ nativeOriginalIntegerDriveLaplace nativeLaplaceContinuationDomain :=
    fun _ hz => nativeOriginalIntegerDriveLaplace_analyticAt hz.1
  have hg : AnalyticOnNhd ℂ
      (fun z : ℂ => -deriv riemannZeta (z + 1 / 2) * nativeOriginalSourceLaplace z)
      nativeLaplaceContinuationDomain := by
    intro z hz
    have hzeta : z + 1 / 2 ≠ 1 := by
      intro h
      apply hz.2
      linear_combination h
    have harg : AnalyticAt ℂ (fun y : ℂ => y + 1 / 2) z := analyticAt_id.add analyticAt_const
    have hdz : AnalyticAt ℂ (fun y : ℂ => deriv riemannZeta (y + 1 / 2)) z :=
      AnalyticAt.comp (f := fun y : ℂ => y + 1 / 2) (x := z)
        (analyticOn_riemannZeta (z + 1 / 2) hzeta).deriv harg
    exact hdz.neg.mul (nativeOriginalSourceLaplace_analyticAt z)
  exact nativeLaplace_eqOn_of_eqOn_rightHalfPlane ha hg
    (fun z hz => nativeOriginalIntegerDrive_complexLaplace_of_half_lt_re hz) ⟨hw, hne⟩

/-- Literal Y=c*U, with both arithmetic and physical-source factors paid. -/
theorem nativeCompletedInput_complexLaplace {w : ℂ} (hw : 0 < w.re)
    (hne : w ≠ 1 / 2) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeCompletedInput t : ℂ)) =
      nativeCompletionRationalMultiplier w * (-deriv riemannZeta (w + 1 / 2)) *
        nativeOriginalSourceLaplace w := by
  rw [nativeCompletedInput_complexLaplace_eq_c_mul_drive hw.le,
    nativeOriginalIntegerDrive_complexLaplace hw hne, mul_assoc]

/-- The literal stable input is zero at this damping; no totalized
zeta-prime expression at its pole is substituted to obtain the value. -/
theorem nativeCompletedInput_complexLaplace_half :
    (∫ t : ℝ, Complex.exp (-(1 / 2 : ℂ) * (t : ℂ)) * (nativeCompletedInput t : ℂ)) = 0 := by
  rw [nativeCompletedInput_complexLaplace_eq_c_mul_drive (by norm_num)]
  norm_num [nativeCompletionRationalMultiplier]

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalIntegerDriveLaplace_analyticAt
#print axioms Zeta23.CCM.nativeOriginalSourceLaplace_analyticAt
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_complexLaplace
#print axioms Zeta23.CCM.nativeCompletedInput_complexLaplace
#print axioms Zeta23.CCM.nativeCompletedInput_complexLaplace_half
