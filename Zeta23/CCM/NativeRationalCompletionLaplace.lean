import Zeta23.CCM.NativeFloorCompletionSource

/-!
# The native causal rational kernel has its actual real Laplace multiplier

This calculation concerns `c`, before the integer action. Its negative
signed integral is deliberately retained. It supplies no global exchange of
the integer sum with integration, no mass bound for `a = c*N`, and no inverse.
-/

noncomputable section

open Set MeasureTheory

namespace Zeta23.CCM

theorem nativeRationalCausalKernel_damped_eq {t : ℝ} (ht : 0 ≤ t) (σ : ℝ) :
    Real.exp (-σ * t) * nativeRationalCausalKernel t =
      -Real.exp (-(σ + 1 / 2) * t) + 2 * Real.exp (-(σ + 3 / 2) * t) := by
  unfold nativeRationalCausalKernel
  rw [if_pos ht]
  have hfirst : Real.exp (-σ * t) * Real.exp (-(t / 2)) =
      Real.exp (-(σ + 1 / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsecond : Real.exp (-σ * t) * Real.exp (-(3 * t / 2)) =
      Real.exp (-(σ + 3 / 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = -(Real.exp (-σ * t) * Real.exp (-(t / 2))) +
      2 * (Real.exp (-σ * t) * Real.exp (-(3 * t / 2))) := by ring
    _ = _ := by rw [hfirst, hsecond]

theorem nativeRationalCausalKernel_damped_integrableOn {σ : ℝ} (hσ : -1 / 2 < σ) :
    IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * nativeRationalCausalKernel t) (Ioi 0) := by
  have hfirst := integrableOn_exp_mul_Ioi (a := -(σ + 1 / 2)) (by linarith) 0
  have hsecond := integrableOn_exp_mul_Ioi (a := -(σ + 3 / 2)) (by linarith) 0
  exact (hfirst.neg.add (hsecond.const_mul (2 : ℝ))).congr_fun
    (fun t ht => (nativeRationalCausalKernel_damped_eq (mem_Ioi.mp ht).le σ).symm)
    measurableSet_Ioi

/-- The multiplier is derived from two genuinely integrable exponentials. -/
theorem nativeRationalCausalKernel_realLaplace {σ : ℝ} (hσ : -1 / 2 < σ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-σ * t) * nativeRationalCausalKernel t) =
      (σ - 1 / 2) / ((σ + 1 / 2) * (σ + 3 / 2)) := by
  have hfirst := integrableOn_exp_mul_Ioi (a := -(σ + 1 / 2)) (by linarith) 0
  have hsecond := integrableOn_exp_mul_Ioi (a := -(σ + 3 / 2)) (by linarith) 0
  have heq : (fun t : ℝ => Real.exp (-σ * t) * nativeRationalCausalKernel t) =ᵐ[
      volume.restrict (Ioi 0)]
      (fun t : ℝ => -Real.exp (-(σ + 1 / 2) * t) +
        2 * Real.exp (-(σ + 3 / 2) * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact nativeRationalCausalKernel_damped_eq (mem_Ioi.mp ht).le σ
  have hneg : IntegrableOn (fun t : ℝ => -Real.exp (-(σ + 1 / 2) * t)) (Ioi 0) :=
    hfirst.neg
  have htwice : IntegrableOn (fun t : ℝ => 2 * Real.exp (-(σ + 3 / 2) * t)) (Ioi 0) :=
    hsecond.const_mul (2 : ℝ)
  rw [integral_congr_ae heq, integral_add hneg htwice,
    integral_neg, integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -(σ + 1 / 2) < 0),
    integral_exp_mul_Ioi (by linarith : -(σ + 3 / 2) < 0)]
  have hden1 : σ + 1 / 2 ≠ 0 := ne_of_gt (by linarith)
  have hden2 : σ + 3 / 2 ≠ 0 := ne_of_gt (by linarith)
  simp only [mul_zero, Real.exp_zero]
  field_simp [hden1, hden2]
  ring

/-- The pre-integer-action kernel has negative signed mass. -/
theorem nativeRationalCausalKernel_signed_integral :
    (∫ t : ℝ in Ioi 0, nativeRationalCausalKernel t) = -2 / 3 := by
  have h := nativeRationalCausalKernel_realLaplace (σ := 0) (by norm_num)
  norm_num at h
  simpa only [neg_div] using h

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeRationalCausalKernel_damped_integrableOn
#print axioms Zeta23.CCM.nativeRationalCausalKernel_realLaplace
#print axioms Zeta23.CCM.nativeRationalCausalKernel_signed_integral
