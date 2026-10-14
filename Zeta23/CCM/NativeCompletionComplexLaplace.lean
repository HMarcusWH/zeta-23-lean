import Zeta23.CCM.NativeRationalCompletionLaplace
import Zeta23.CCM.NativeCompletionIntegerKernel

/-!
The actual signed correction kernel has its complex rational multiplier.
This calculation retains its sign and the zero at w=1/2. The integer
completion's zeta multiplier is a separate analytic obligation.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

def nativeCompletionRationalMultiplier (w : ℂ) : ℂ :=
  (w - 1 / 2) / ((w + 1 / 2) * (w + 3 / 2))

theorem nativeRationalCausalKernel_complexDamped_eq {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    Complex.exp (-w * (t : ℂ)) * (nativeRationalCausalKernel t : ℂ) =
      -Complex.exp (-(w + 1 / 2) * (t : ℂ)) +
        2 * Complex.exp (-(w + 3 / 2) * (t : ℂ)) := by
  have hk : (nativeRationalCausalKernel t : ℂ) =
      -Complex.exp (-((t : ℂ) / 2)) + 2 * Complex.exp (-(3 * (t : ℂ) / 2)) := by
    simp [nativeRationalCausalKernel, ht, Complex.ofReal_exp]
  have hfirst : Complex.exp (-w * (t : ℂ)) * Complex.exp (-((t : ℂ) / 2)) =
      Complex.exp (-(w + 1 / 2) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hsecond : Complex.exp (-w * (t : ℂ)) * Complex.exp (-(3 * (t : ℂ) / 2)) =
      Complex.exp (-(w + 3 / 2) * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hk]
  calc
    _ = -(Complex.exp (-w * (t : ℂ)) * Complex.exp (-((t : ℂ) / 2))) +
        2 * (Complex.exp (-w * (t : ℂ)) * Complex.exp (-(3 * (t : ℂ) / 2))) := by ring
    _ = _ := by rw [hfirst, hsecond]

theorem nativeRationalCausalKernel_complexDamped_integrableOn {w : ℂ}
    (hw : -1 / 2 < w.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-w * (t : ℂ)) *
      (nativeRationalCausalKernel t : ℂ)) (Ioi 0) := by
  have hfirst : (-(w + 1 / 2)).re < 0 := by
    have : (-(w + 1 / 2)).re = -(w.re + 1 / 2) := by norm_num
    rw [this]
    linarith
  have hsecond : (-(w + 3 / 2)).re < 0 := by
    have : (-(w + 3 / 2)).re = -(w.re + 3 / 2) := by norm_num
    rw [this]
    linarith
  exact ((integrableOn_exp_mul_complex_Ioi hfirst 0).neg.add
    ((integrableOn_exp_mul_complex_Ioi hsecond 0).const_mul (2 : ℂ))).congr_fun
    (fun t ht => (nativeRationalCausalKernel_complexDamped_eq (mem_Ioi.mp ht).le w).symm)
    measurableSet_Ioi

theorem nativeRationalCausalKernel_complexLaplace {w : ℂ} (hw : -1 / 2 < w.re) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-w * (t : ℂ)) *
      (nativeRationalCausalKernel t : ℂ)) = nativeCompletionRationalMultiplier w := by
  have hfirst : (-(w + 1 / 2)).re < 0 := by
    have : (-(w + 1 / 2)).re = -(w.re + 1 / 2) := by norm_num
    rw [this]
    linarith
  have hsecond : (-(w + 3 / 2)).re < 0 := by
    have : (-(w + 3 / 2)).re = -(w.re + 3 / 2) := by norm_num
    rw [this]
    linarith
  have heq : (fun t : ℝ => Complex.exp (-w * (t : ℂ)) *
      (nativeRationalCausalKernel t : ℂ)) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => -Complex.exp (-(w + 1 / 2) * (t : ℂ)) +
        2 * Complex.exp (-(w + 3 / 2) * (t : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact nativeRationalCausalKernel_complexDamped_eq (mem_Ioi.mp ht).le w
  have hneg : IntegrableOn (fun t : ℝ => -Complex.exp (-(w + 1 / 2) * (t : ℂ)))
      (Ioi 0) := (integrableOn_exp_mul_complex_Ioi hfirst 0).neg
  have htwice : IntegrableOn (fun t : ℝ => 2 * Complex.exp (-(w + 3 / 2) * (t : ℂ)))
      (Ioi 0) := (integrableOn_exp_mul_complex_Ioi hsecond 0).const_mul (2 : ℂ)
  rw [integral_congr_ae heq, integral_add hneg htwice,
    integral_neg, integral_const_mul, integral_exp_mul_complex_Ioi hfirst,
    integral_exp_mul_complex_Ioi hsecond]
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
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    nativeCompletionRationalMultiplier, neg_div_neg_eq]
  rw [← neg_div, mul_one_div, div_add_div _ _ hd1 hd2]
  congr 1
  ring

theorem nativeCompletionCorrection_complexLaplace {w : ℂ} (hw : -1 / 2 < w.re) :
    (∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeCompletionCorrection t : ℂ)) =
      nativeCompletionRationalMultiplier w := by
  rw [nativeCompletionCorrection_eq_rationalKernel]
  have hs : (∫ t : ℝ in Ici 0, Complex.exp (-w * (t : ℂ)) *
      (nativeRationalCausalKernel t : ℂ)) =
      ∫ t : ℝ, Complex.exp (-w * (t : ℂ)) * (nativeRationalCausalKernel t : ℂ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [nativeRationalCausalKernel_zero_of_neg (lt_of_not_ge ht)]
    simp
  rw [← hs, integral_Ici_eq_integral_Ioi]
  exact nativeRationalCausalKernel_complexLaplace hw

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeRationalCausalKernel_complexDamped_integrableOn
#print axioms Zeta23.CCM.nativeRationalCausalKernel_complexLaplace
#print axioms Zeta23.CCM.nativeCompletionCorrection_complexLaplace
