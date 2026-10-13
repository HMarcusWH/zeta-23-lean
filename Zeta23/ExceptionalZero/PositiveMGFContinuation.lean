import Zeta23.ExceptionalZero.PositiveMomentSeries
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Exponential integrability supplied by an actual MGF continuation

An analytic continuation of the complex moment-generating function to a
disk about an interior base point has Taylor coefficients given by the
actual moments. At a nonnegative real point in that disk, the positive
moment-series lemma turns Taylor convergence into exponential integrability.

The base point here is zero; a positive Laplace measure can be tilted at an
interior point before applying this result. No Taylor summability or desired
boundary singularity is accepted as a caller premise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Nat

namespace Zeta23.ExceptionalZero

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {H : ℂ → ℂ} {r h b : ℝ}

/-- The actual Taylor coefficients of a continuation agreeing with the
complex MGF near zero are the integrated real moments. -/
theorem iteratedDeriv_eq_moment_of_complexMGF_continuation
    (h0 : 0 ∈ interior (integrableExpSet X μ))
    (hagree : H =ᶠ[𝓝 (0 : ℂ)] complexMGF X μ) (n : ℕ) :
    iteratedDeriv n H 0 = ((∫ ω, X ω ^ n ∂μ : ℝ) : ℂ) := by
  have h0c : (0 : ℂ).re ∈ interior (integrableExpSet X μ) := by
    simpa only [Complex.zero_re] using h0
  rw [hagree.iteratedDeriv_eq n, iteratedDeriv_complexMGF h0c n]
  simp only [zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow,
    integral_complex_ofReal]

/-- Taylor convergence of an actual continuation supplies summability of
the integrated moment series. No positivity assumption is needed here. -/
theorem summable_moments_of_complexMGF_continuation
    (h0 : 0 ∈ interior (integrableExpSet X μ))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 r))
    (hagree : H =ᶠ[𝓝 (0 : ℂ)] complexMGF X μ)
    (hball : (h : ℂ) ∈ Metric.ball 0 r) :
    Summable (fun n : ℕ =>
      (h ^ n / (n ! : ℝ)) * ∫ ω, X ω ^ n ∂μ) := by
  apply Complex.summable_ofReal.mp
  refine (Complex.hasSum_taylorSeries_on_ball hH hball).summable.congr ?_
  intro n
  rw [iteratedDeriv_eq_moment_of_complexMGF_continuation h0 hagree n]
  simp only [sub_zero, smul_eq_mul]
  push_cast
  ring

/-- A continuation disk about zero supplies actual exponential integrability
at every nonnegative real point strictly inside the disk. -/
theorem integrable_exp_mul_of_complexMGF_continuation
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (h0 : 0 ∈ interior (integrableExpSet X μ))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 r))
    (hagree : H =ᶠ[𝓝 (0 : ℂ)] complexMGF X μ)
    (hh : 0 ≤ h) (hr : h < r) :
    Integrable (fun ω => Real.exp (h * X ω)) μ := by
  have hball : (h : ℂ) ∈ Metric.ball 0 r := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_of_nonneg hh] using hr
  exact integrable_exp_mul_of_summable_positive_moments hX hh
    (integrable_pow_of_mem_interior_integrableExpSet h0)
    (summable_moments_of_complexMGF_continuation h0 hH hagree hball)

/-- If the continuation disk reaches past a nonnegative threshold, there
is actual exponential integrability strictly beyond that threshold.
The threshold can in particular be a previously established upper boundary. -/
theorem exists_integrable_exp_mul_gt_of_complexMGF_continuation
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (h0 : 0 ∈ interior (integrableExpSet X μ))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 r))
    (hagree : H =ᶠ[𝓝 (0 : ℂ)] complexMGF X μ)
    (hb : 0 ≤ b) (hbr : b < r) :
    ∃ t : ℝ, b < t ∧ Integrable (fun ω => Real.exp (t * X ω)) μ := by
  refine ⟨(b + r) / 2, ?_, ?_⟩
  · linarith
  · exact integrable_exp_mul_of_complexMGF_continuation hX h0 hH hagree
      (by linarith) (by linarith)

#print axioms iteratedDeriv_eq_moment_of_complexMGF_continuation
#print axioms summable_moments_of_complexMGF_continuation
#print axioms integrable_exp_mul_of_complexMGF_continuation
#print axioms exists_integrable_exp_mul_gt_of_complexMGF_continuation

end Zeta23.ExceptionalZero
