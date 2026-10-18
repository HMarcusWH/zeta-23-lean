import Zeta23.CCM.NativeCompletedInputComplexLaplace
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex

/-!
The actual integer completion of the signed correction kernel has the
zeta multiplier in its half-plane of absolute convergence. Every term is
integrable and the integrals of the norms are summable before exchanging
the native integer history and the full-line integral.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Zeta23.CCM

def nativeIntegerLaplaceCoefficient (w : ℂ) (n : ℕ) : ℂ :=
  (nativeIntegerCoefficient n : ℂ) * Complex.exp (-w * (Real.log n : ℂ))

theorem nativeIntegerLaplaceCoefficient_eq_cpow {w : ℂ} (hw : 1 / 2 < w.re) (n : ℕ) :
    nativeIntegerLaplaceCoefficient w n = 1 / (n : ℂ) ^ (w + 1 / 2) := by
  by_cases hn : n = 0
  · subst n
    have hs : w + 1 / 2 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
      linarith
    simp only [nativeIntegerLaplaceCoefficient, nativeIntegerCoefficient,
      Nat.cast_zero, Real.sqrt_zero, div_zero, Complex.ofReal_zero, zero_mul]
    rw [Complex.zero_cpow hs, div_zero]
  · have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hrootreal : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnreal]
      congr 1
      ring
    have hroot : (Real.sqrt (n : ℝ) : ℂ) = Complex.exp ((Real.log n : ℂ) / 2) := by
      rw [hrootreal, Complex.ofReal_exp]
      push_cast
      rfl
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    unfold nativeIntegerLaplaceCoefficient nativeIntegerCoefficient
    rw [Complex.ofReal_div, Complex.ofReal_one, hroot,
      Complex.cpow_def_of_ne_zero hnc]
    simp only [one_div, ← Complex.exp_neg]
    rw [← Complex.exp_add, ← Complex.natCast_log]
    congr 1
    ring

theorem nativeIntegerLaplaceCoefficient_summable_norm {w : ℂ} (hw : 1 / 2 < w.re) :
    Summable (fun n : ℕ => ‖nativeIntegerLaplaceCoefficient w n‖) := by
  simp_rw [nativeIntegerLaplaceCoefficient_eq_cpow hw]
  apply summable_norm_iff.mpr
  apply Complex.summable_one_div_nat_cpow.mpr
  simp only [Complex.add_re]
  norm_num
  linarith

theorem nativeIntegerLaplaceCoefficient_tsum {w : ℂ} (hw : 1 / 2 < w.re) :
    (∑' n : ℕ, nativeIntegerLaplaceCoefficient w n) = riemannZeta (w + 1 / 2) := by
  simp_rw [nativeIntegerLaplaceCoefficient_eq_cpow hw]
  symm
  apply zeta_eq_tsum_one_div_nat_cpow
  simp only [Complex.add_re]
  norm_num
  linarith

private def integerKernelLaplaceTerm (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-w * (t : ℂ)) *
    (nativeIntegerCoefficient n * nativeRationalCausalKernel (t - Real.log n) : ℝ)

private theorem integerKernelLaplaceTerm_factor (w : ℂ) (n : ℕ) (t : ℝ) :
    integerKernelLaplaceTerm w n t = nativeIntegerLaplaceCoefficient w n *
      nativeCausalComplexDamping w nativeRationalCausalKernel (t - Real.log n) := by
  have hexp : Complex.exp (-w * (t : ℂ)) =
      Complex.exp (-w * (Real.log n : ℂ)) *
        Complex.exp (-w * ((t - Real.log n : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [integerKernelLaplaceTerm, nativeIntegerLaplaceCoefficient,
    nativeCausalComplexDamping, Complex.ofReal_mul]
  rw [hexp]
  ring

theorem nativePositiveCompletion_complexLaplace_of_half_lt_re {w : ℂ}
    (hw : 1 / 2 < w.re) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativePositiveCompletion t : ℂ)) =
      nativeCompletionRationalMultiplier w * riemannZeta (w + 1 / 2) := by
  let b := nativeCausalComplexDamping w nativeRationalCausalKernel
  have hkernel : Integrable nativeRationalCausalKernel := by
    simpa only [nativeCompletionCorrection_eq_rationalKernel] using nativeCompletionCorrection_integrable
  have hb : Integrable b := nativeCausalComplexDamping_integrable (by linarith) hkernel
    (fun t ht => nativeRationalCausalKernel_zero_of_neg ht)
  have hfactor (n : ℕ) (t : ℝ) : integerKernelLaplaceTerm w n t =
      nativeIntegerLaplaceCoefficient w n * b (t - Real.log n) :=
    integerKernelLaplaceTerm_factor w n t
  have hterm (n : ℕ) : Integrable (integerKernelLaplaceTerm w n) :=
    ((hb.comp_sub_right (Real.log n)).const_mul (nativeIntegerLaplaceCoefficient w n)).congr
      (Filter.Eventually.of_forall fun t => (hfactor n t).symm)
  have hnorm (n : ℕ) : (∫ t : ℝ, ‖integerKernelLaplaceTerm w n t‖) =
      ‖nativeIntegerLaplaceCoefficient w n‖ * ∫ t : ℝ, ‖b t‖ := by
    simp_rw [hfactor, norm_mul]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun t : ℝ => ‖b t‖) (Real.log n)
  have hnormsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖integerKernelLaplaceTerm w n t‖) := by
    simp_rw [hnorm]
    exact (nativeIntegerLaplaceCoefficient_summable_norm hw).mul_right _
  have hint (n : ℕ) : (∫ t : ℝ, integerKernelLaplaceTerm w n t) =
      nativeIntegerLaplaceCoefficient w n * ∫ t : ℝ, b t := by
    simp_rw [hfactor]
    rw [integral_const_mul, integral_sub_right_eq_self]
  have hsum := hasSum_integral_of_summable_integral_norm hterm hnormsum
  have hpoint (t : ℝ) : Complex.exp (-w * (t : ℂ)) * (nativePositiveCompletion t : ℂ) =
      ∑' n : ℕ, integerKernelLaplaceTerm w n t := by
    rw [← nativeIntegerTranslateAction_rationalKernel_eq_positiveCompletion t]
    simp only [nativeIntegerTranslateAction, Complex.ofReal_tsum]
    rw [← tsum_mul_left]
    rfl
  calc
    _ = ∫ t : ℝ, ∑' n : ℕ, integerKernelLaplaceTerm w n t :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' n : ℕ, ∫ t : ℝ, integerKernelLaplaceTerm w n t := hsum.tsum_eq.symm
    _ = (∑' n : ℕ, nativeIntegerLaplaceCoefficient w n) * ∫ t : ℝ, b t := by
      simp_rw [hint]
      rw [tsum_mul_right]
    _ = _ := by
      rw [nativeIntegerLaplaceCoefficient_tsum hw]
      have hc := nativeCompletionCorrection_complexLaplace (w := w) (by linarith)
      rw [nativeCompletionCorrection_eq_rationalKernel] at hc
      change (∫ t : ℝ, b t) = nativeCompletionRationalMultiplier w at hc
      rw [hc]
      ring

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeIntegerLaplaceCoefficient_eq_cpow
#print axioms Zeta23.CCM.nativeIntegerLaplaceCoefficient_summable_norm
#print axioms Zeta23.CCM.nativeIntegerLaplaceCoefficient_tsum
#print axioms Zeta23.CCM.nativePositiveCompletion_complexLaplace_of_half_lt_re
