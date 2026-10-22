import Zeta23.OPICAFollowup.AuxiliaryCompletions

/-! Independent expected statements and actual-domain/boundary uses for the
three original auxiliary-completion roots. No theorem type is inferred or
reconstructed from a compiler reflection API. -/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology FourierTransform
open Zeta23.OPICAFollowup
namespace OPICARepairExpected

example :
    (∀ k : ℕ, ∀ z : ℂ, -((k:ℝ)+3/2)<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionFilter k t:ℂ)) ∧
      (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(auxCompletionFilter k t:ℂ))=auxRationalFactor k z) ∧
    (∀ k : ℕ, ∀ z : ℂ, 1/2<z.re →
      auxCompletionLaplace k z=auxRationalFactor k z*riemannZeta (z+1/2)) ∧
    (∀ k : ℕ, 1≤k → ∀ z : ℂ, -((k:ℝ)+1/2)<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionKernel k t:ℂ)) ∧
      AnalyticAt ℂ (auxCompletionLaplace k) z ∧
      auxCompletionLaplace k z=auxCompletionFilledTransform k z) ∧
    (∀ k : ℕ, 1≤k → auxCompletionLaplace k (1/2)=
      (Nat.factorial (k+1):ℂ)/(Nat.factorial (2*k+3):ℂ)) := by
  exact aux_completion_actual_transform

example (k : ℕ) (hk : 1≤k) :
    (∀ t : ℝ, Summable (fun n : ℤ =>
      𝓕 (auxScaledProfile k (Real.exp (-t))) n)) ∧
    (∀ t : ℝ, |auxCompletionKernel k t|≤
      auxCompletionBound k*Real.exp (-((k:ℝ)+1/2)*t)) := by
  exact aux_completion_uniform_decay k hk

example (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    ∃ Cp : ℝ, 0<Cp ∧ ∀ k : ℕ, 1≤k →
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤2/(Nat.factorial (k+1):ℝ) ∧
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)/‖auxRationalFactor k ((rho:ℂ)-1/2)‖≤
        Real.exp (Cp*(k+1)) ∧
      Real.exp (-(k:ℝ)*Real.log (k+1)-Cp*(k+1))≤
        ‖auxRationalFactor k ((rho:ℂ)-1/2)‖/auxCompletionBound k := by
  exact aux_completion_ratio_bounds rho hright

/-- Actual half-point value, not a cancelled meromorphic-expression value. -/
example : auxCompletionLaplace 1 (1/2)=1/60 := by
  have h := aux_completion_actual_transform.2.2.2 1 (by norm_num)
  norm_num at h ⊢
  exact h

/-- Original filter identity still covers order zero and its full safe domain. -/
example (z : ℂ) (hz : -(3/2:ℝ)<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionFilter 0 t:ℂ)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(auxCompletionFilter 0 t:ℂ))=
      auxRationalFactor 0 z := by
  exact aux_completion_actual_transform.1 0 z (by simpa using hz)

/-- The improved kernel domain extends strictly left of the original half-plane. -/
example : AnalyticAt ℂ (auxCompletionLaplace 2) (-2:ℂ) := by
  exact (aux_completion_actual_transform.2.2.1 2 (by norm_num) (-2) (by norm_num [auxCompletionAlpha])).2.1

example (k : ℕ) (hk : 1≤k) (epsilon : ℝ) (he : -((k:ℝ)+1/2)<epsilon) :
    MemLp (Zeta23.OPICA.weightedCausalProfile epsilon
      (fun t => (auxCompletionKernel k t:ℂ))) 2 volume := by
  exact auxCompletion_weightedL2 k hk epsilon he

/-- Explicit negative frequency is included, and zero frequency is treated separately. -/
example (k : ℕ) (xi : ℝ) (hxi : xi<0) :
    ‖auxProfileFourierIntegral k xi‖≤
      (1+(2:ℝ)^(3*k+4))/(2*Real.pi*|xi|)^(k+1) := by
  exact auxCompletionProfile_fourier_decay k xi (ne_of_lt hxi)

example (k : ℕ) : auxProfileFourierIntegral k 0=0 := auxProfileFourier_zero k

example (psi : ℝ→ℂ) (hpsi : ContDiff ℝ (⊤:ℕ∞) psi) :
    (-1:ℂ)*(∫ u : ℝ,(auxCompletionProfile 0 u:ℂ)*deriv psi u)=
      (∫ u : ℝ in 0..1, Complex.ofReal ((auxProfilePolynomial 0).derivative.eval u)*psi u)-psi 1 := by
  simpa only [Nat.zero_add,Function.iterate_one,iteratedDeriv_one,pow_one,neg_mul,
    one_mul,sub_eq_add_neg] using auxCompletionProfile_distributional_derivative 0 psi hpsi

#print axioms Zeta23.OPICAFollowup.aux_completion_actual_transform
#print axioms Zeta23.OPICAFollowup.aux_completion_uniform_decay
#print axioms Zeta23.OPICAFollowup.aux_completion_ratio_bounds
#print axioms Zeta23.OPICAFollowup.auxCompletionProfile_distributional_derivative
#print axioms Zeta23.OPICAFollowup.auxCompletionKernel_scaled_profile
#print axioms Zeta23.OPICAFollowup.auxCompletionFilledTransform_at_half
end OPICARepairExpected
