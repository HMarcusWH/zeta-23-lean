import Zeta23.CCM.NativeIntegerKernelComplexLaplace
import Zeta23.ExceptionalZero.NativeOriginalSourceLaplaceVisibility
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv

/-!
The unchanged logarithmic integer drive has its actual -zeta' times J
multiplier on the absolute-convergence half-plane. The source is the
literal j=P²q with one Q factor. Norm summability is proved before Fubini.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Zeta23.CCM

def nativeIntegerDriveLaplaceCoefficient (w : ℂ) (n : ℕ) : ℂ :=
  (nativeIntegerDriveCoefficient n : ℂ) * Complex.exp (-w * (Real.log n : ℂ))

theorem nativeIntegerDriveLaplaceCoefficient_eq_term {w : ℂ} (hw : 1 / 2 < w.re) (n : ℕ) :
    nativeIntegerDriveLaplaceCoefficient w n =
      LSeries.term (LSeries.logMul 1) (w + 1 / 2) n := by
  have hfactor : nativeIntegerDriveLaplaceCoefficient w n =
      (Real.log n : ℂ) * nativeIntegerLaplaceCoefficient w n := by
    simp only [nativeIntegerDriveLaplaceCoefficient, nativeIntegerDriveCoefficient,
      nativeIntegerLaplaceCoefficient, nativeIntegerCoefficient, Complex.ofReal_div,
      Complex.ofReal_one]
    ring
  rw [hfactor]
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero]
  · rw [nativeIntegerLaplaceCoefficient_eq_cpow hw, LSeries.term_of_ne_zero hn]
    simp only [LSeries.logMul, Pi.one_apply, mul_one, Complex.natCast_log]
    ring

private theorem drive_abscissa {w : ℂ} (hw : 1 / 2 < w.re) :
    LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < (w + 1 / 2).re := by
  rw [LSeries.abscissaOfAbsConv_one]
  have hs : (1 : ℝ) < (w + 1 / 2).re := by norm_num; linarith
  exact_mod_cast hs

theorem nativeIntegerDriveLaplaceCoefficient_summable_norm {w : ℂ} (hw : 1 / 2 < w.re) :
    Summable (fun n : ℕ => ‖nativeIntegerDriveLaplaceCoefficient w n‖) := by
  have h := LSeriesSummable_logMul_of_lt_re (drive_abscissa hw)
  change Summable (fun n : ℕ => LSeries.term (LSeries.logMul 1) (w + 1 / 2) n) at h
  simp_rw [nativeIntegerDriveLaplaceCoefficient_eq_term hw]
  exact summable_norm_iff.mpr h

theorem nativeIntegerDriveLaplaceCoefficient_tsum {w : ℂ} (hw : 1 / 2 < w.re) :
    (∑' n : ℕ, nativeIntegerDriveLaplaceCoefficient w n) = -deriv riemannZeta (w + 1 / 2) := by
  have heq : (∑' n : ℕ, nativeIntegerDriveLaplaceCoefficient w n) =
      LSeries (LSeries.logMul 1) (w + 1 / 2) := by
    simp_rw [nativeIntegerDriveLaplaceCoefficient_eq_term hw]
    rfl
  have hs : (1 : ℝ) < (w + 1 / 2).re := by norm_num; linarith
  have hderiv : deriv (LSeries 1) (w + 1 / 2) = deriv riemannZeta (w + 1 / 2) := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{z : ℂ | 1 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs,
      fun _ => LSeries_one_eq_riemannZeta⟩
  rw [heq, ← hderiv, LSeries_deriv (drive_abscissa hw), neg_neg]

theorem nativeOriginalSource_complexDamping_integrable (w : ℂ) :
    Integrable (nativeCausalComplexDamping w nativeOriginalSource) := by
  have hj : HasCompactSupport (fun t : ℝ => (nativeOriginalSource t : ℂ)) := by
    apply HasCompactSupport.intro
      (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale) isCompact_Icc
    intro t ht
    rw [nativeOriginalSource_supported t ht, Complex.ofReal_zero]
  have hc : Continuous (nativeCausalComplexDamping w nativeOriginalSource) :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-w * (t : ℂ)))).mul
      (Complex.continuous_ofReal.comp nativeOriginalSource_contDiff.continuous)
  exact hc.integrable_of_hasCompactSupport hj.mul_left

private def integerDriveLaplaceTerm (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-w * (t : ℂ)) *
    (nativeIntegerDriveCoefficient n * nativeOriginalSource (t - Real.log n) : ℝ)

private theorem integerDriveLaplaceTerm_factor (w : ℂ) (n : ℕ) (t : ℝ) :
    integerDriveLaplaceTerm w n t = nativeIntegerDriveLaplaceCoefficient w n *
      nativeCausalComplexDamping w nativeOriginalSource (t - Real.log n) := by
  have hexp : Complex.exp (-w * (t : ℂ)) =
      Complex.exp (-w * (Real.log n : ℂ)) *
        Complex.exp (-w * ((t - Real.log n : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [integerDriveLaplaceTerm, nativeIntegerDriveLaplaceCoefficient,
    nativeCausalComplexDamping, Complex.ofReal_mul]
  rw [hexp]
  ring

theorem nativeOriginalIntegerDrive_complexLaplace_of_half_lt_re {w : ℂ}
    (hw : 1 / 2 < w.re) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeOriginalIntegerDrive t : ℂ)) =
      -deriv riemannZeta (w + 1 / 2) * nativeOriginalSourceLaplace w := by
  let b := nativeCausalComplexDamping w nativeOriginalSource
  have hb : Integrable b := nativeOriginalSource_complexDamping_integrable w
  have hfactor (n : ℕ) (t : ℝ) : integerDriveLaplaceTerm w n t =
      nativeIntegerDriveLaplaceCoefficient w n * b (t - Real.log n) :=
    integerDriveLaplaceTerm_factor w n t
  have hterm (n : ℕ) : Integrable (integerDriveLaplaceTerm w n) :=
    ((hb.comp_sub_right (Real.log n)).const_mul (nativeIntegerDriveLaplaceCoefficient w n)).congr
      (Filter.Eventually.of_forall fun t => (hfactor n t).symm)
  have hnorm (n : ℕ) : (∫ t : ℝ, ‖integerDriveLaplaceTerm w n t‖) =
      ‖nativeIntegerDriveLaplaceCoefficient w n‖ * ∫ t : ℝ, ‖b t‖ := by
    simp_rw [hfactor, norm_mul]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun t : ℝ => ‖b t‖) (Real.log n)
  have hnormsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖integerDriveLaplaceTerm w n t‖) := by
    simp_rw [hnorm]
    exact (nativeIntegerDriveLaplaceCoefficient_summable_norm hw).mul_right _
  have hint (n : ℕ) : (∫ t : ℝ, integerDriveLaplaceTerm w n t) =
      nativeIntegerDriveLaplaceCoefficient w n * ∫ t : ℝ, b t := by
    simp_rw [hfactor]
    rw [integral_const_mul, integral_sub_right_eq_self]
  have hsum := hasSum_integral_of_summable_integral_norm hterm hnormsum
  have hpoint (t : ℝ) : Complex.exp (-w * (t : ℂ)) * (nativeOriginalIntegerDrive t : ℂ) =
      ∑' n : ℕ, integerDriveLaplaceTerm w n t := by
    simp only [nativeOriginalIntegerDrive, nativeIntegerDriveField, Complex.ofReal_tsum]
    rw [← tsum_mul_left]
    rfl
  calc
    _ = ∫ t : ℝ, ∑' n : ℕ, integerDriveLaplaceTerm w n t :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' n : ℕ, ∫ t : ℝ, integerDriveLaplaceTerm w n t := hsum.tsum_eq.symm
    _ = (∑' n : ℕ, nativeIntegerDriveLaplaceCoefficient w n) * ∫ t : ℝ, b t := by
      simp_rw [hint]
      rw [tsum_mul_right]
    _ = _ := by rw [nativeIntegerDriveLaplaceCoefficient_tsum hw]; rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeIntegerDriveLaplaceCoefficient_eq_term
#print axioms Zeta23.CCM.nativeIntegerDriveLaplaceCoefficient_summable_norm
#print axioms Zeta23.CCM.nativeIntegerDriveLaplaceCoefficient_tsum
#print axioms Zeta23.CCM.nativeOriginalSource_complexDamping_integrable
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_complexLaplace_of_half_lt_re
