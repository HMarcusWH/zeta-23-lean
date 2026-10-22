import Zeta23.OPICAFollowup.MultiplicityTail

/-! Independent full-scope Laguerre norm and physical-domain consumers.
The expected type is written explicitly rather than obtained by reflection.
No moment, residual or terminal-memory conclusion is supplied as an input. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped Topology
open Zeta23.OPICAFollowup
namespace OPICAMultiplicityExpected

example (m : ℕ) (hm : 1 ≤ m) (p : ℂ) (hp : 0 < p.re) (T : ℝ) :
    (monicLaguerre (m-1)).Monic ∧
    (∀ Q : Polynomial ℝ, Q.natDegree < m-1 →
      laguerreWeightedPair (monicLaguerre (m-1)) Q = 0) ∧
    MemLp (monicLaguerreTail (m-1) p T) 2 volume ∧
    (monicLaguerreTailL2 (m-1) p T hp : ℝ → ℂ) =ᵐ[volume]
      monicLaguerreTail (m-1) p T ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖^2 =
      Real.exp (-2*p.re*T)*((m-1).factorial:ℝ)^2/(2*p.re)^(2*(m-1)+1) ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖ =
      Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2) := by
  exact laguerre_tail_norm m hm p hp T

/-- The degree-zero test is the literal constant polynomial. -/
example : monicLaguerre 0 = (1 : Polynomial ℝ) := by
  simp [monicLaguerre]

/-- The pointwise representative retains the conjugation and real shift. -/
example (n : ℕ) (p : ℂ) (T t : ℝ) (ht : T ≤ t) :
    monicLaguerreTail n p T t =
      (((2*p.re)^n)⁻¹*(monicLaguerre n).eval (2*p.re*(t-T)):ℝ)*
        Complex.exp (-(starRingEnd ℂ p)*(t:ℂ)) := by
  exact Set.indicator_of_mem ht _

example (n : ℕ) (p : ℂ) (T t : ℝ) (ht : t < T) :
    monicLaguerreTail n p T t = 0 := by
  exact Set.indicator_of_notMem (not_le.mpr ht) _

/-- Negative lower endpoints and either sign of the ordinate are permitted. -/
example (tau : ℝ) :
    ‖monicLaguerreTailL2 0 (1 + (tau:ℂ)*Complex.I) (-3) (by simp)‖ =
      Real.exp 3 / (2:ℝ)^(1/2:ℝ) := by
  have h := (laguerre_tail_norm 1 (by norm_num)
    (1 + (tau:ℂ)*Complex.I) (by simp) (-3)).2.2.2.2.2
  norm_num at h ⊢
  exact h

example (n : ℕ) (p : ℂ) (hp : 0 < p.re) (T : ℝ) :
    (∫ t : ℝ, ‖monicLaguerreTail n p T t‖^2) =
      Real.exp (-2*p.re*T)*(n.factorial:ℝ)^2/(2*p.re)^(2*n+1) := by
  exact monicLaguerreTail_integral_norm_sq n p T hp

#print axioms Zeta23.OPICAFollowup.laguerre_tail_norm
#print axioms Zeta23.OPICAFollowup.monicLaguerre_exact_norm_sq
#print axioms Zeta23.OPICAFollowup.monicLaguerre_orthogonality
#print axioms Zeta23.OPICAFollowup.laguerre_iterated_ibp
#print axioms Zeta23.OPICAFollowup.monicLaguerreTail_integral_norm_sq
end OPICAMultiplicityExpected


/-! Independent Stage2 consumers of the actual MultiplicityTail module.
The stated types expand the physical convolution, residual and memory. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.CCM Zeta23.ExceptionalZero

theorem expected_native_auxiliary_top_moment :
    ∀ k d : ℕ, ∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re →
    MemLp (fun t : ℝ => ∫ s : ℝ,
      (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) 2 volume ∧
    (nativeAuxiliaryStableVector k d:NativeCompletionL2)=ᵐ[volume]
      (fun t : ℝ => ∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) ∧
    (∀ t : ℝ,(∫ s : ℝ,(auxCompletionKernel k s:ℂ)*(primeFieldFamily d (t-s):ℂ))=
      ∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) ∧
    ‖nativeAuxiliaryStableVector k d‖≤
      (∫ s : ℝ,‖auxCompletionFilter k s‖)*‖auxiliaryDriveCausalVector d‖ ∧
    (∀ j<zeroMult (rho:ℂ)-1,
      Integrable (fun t : ℝ => (t:ℂ)^j*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
        (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ))) ∧
      (∫ t : ℝ,(t:ℂ)^j*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
        (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=0) ∧
    Integrable (fun t : ℝ => (t:ℂ)^(zeroMult (rho:ℂ)-1)*
      Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
        (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ))) ∧
    (∫ t : ℝ,(t:ℂ)^(zeroMult (rho:ℂ)-1)*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
      (-1:ℂ)^zeroMult (rho:ℂ)*auxRationalFactor k ((rho:ℂ)-1/2)*
        sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ) ∧
    (∫ t : ℝ,(t:ℂ)^(zeroMult (rho:ℂ)-1)*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))≠0 := by
  intro k d rho hright
  exact native_auxiliary_top_moment k d rho hright

theorem expected_actual_auxiliary_factorial_stability : ∀ k d : ℕ,
    ‖nativeAuxiliaryStableVector k d‖≤
      (2/(Nat.factorial (k+1):ℝ))*‖auxiliaryDriveCausalVector d‖ :=
  nativeAuxiliaryStableVector_factorial_bound

theorem expected_actual_logweighted_drive : ∀ d : ℕ, ∀ t : ℝ,
    integerDriveFamily d t=
      ∑' n : ℕ,(Real.log n/Real.sqrt n)*sourceOrderFamily d (t-Real.log n) := by
  intro d t
  rfl

theorem expected_actual_auxiliary_integrand : ∀ k d : ℕ, ∀ t : ℝ,
    Integrable (fun s : ℝ => (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) :=
  nativeAuxiliaryInput_integrand_integrable

theorem expected_actual_auxiliary_safe_laplace : ∀ k d : ℕ, ∀ z : ℂ, 1/2<z.re →
    (∫ t : ℝ,Complex.exp (-z*(t:ℂ))*(∫ s : ℝ,
      (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
      -auxRationalFactor k z*sourceFamilyLaplace d z*deriv riemannZeta (z+1/2) := by
  intro k d z hz
  exact (nativeAuxiliaryInput_initial_laplace k d hz).2

theorem expected_actual_simple_zero_phase : ∀ k d : ℕ, ∀ rho : zetaZeroConfig.carrier,
    1/2<(rho:ℂ).re → zeroMult (rho:ℂ)=1 →
    (∫ t : ℝ,Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
        -auxRationalFactor k ((rho:ℂ)-1/2)*sourceFamilyLaplace d ((rho:ℂ)-1/2)*
          deriv riemannZeta (rho:ℂ) := by
  intro k d rho hright hm
  have h := nativeAuxiliaryMoment_top_value k d rho hright
  simpa only [hm,Nat.sub_self,nativeAuxiliaryMoment,nativeAuxiliaryInput,pow_zero,
    pow_one,one_mul,neg_mul,iteratedDeriv_one] using h

theorem expected_native_auxiliary_tail_residual_lower :
    ∀ k d : ℕ, 1≤k → ∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re → ∀ T : ℝ,
    0<((2*((rho:ℂ)-1/2).re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
      ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
        ((zeroMult (rho:ℂ)-1).factorial:ℝ)) ∧
    MemLp (nativeTruncatedResidual k d T) 2 volume ∧
    (nativeTruncatedResidualVector k d T:NativeCompletionL2)=ᵐ[volume] nativeTruncatedResidual k d T ∧
    (∀ t<T,nativeTruncatedResidual k d T t=0) ∧
    ((2*((rho:ℂ)-1/2).re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
      ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
        ((zeroMult (rho:ℂ)-1).factorial:ℝ))*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
          Real.exp (((rho:ℂ)-1/2).re*T)≤‖(nativeTruncatedResidualVector k d T:NativeCompletionL2)‖ := by
  intro k d hk rho hright T
  exact native_auxiliary_tail_residual_lower k d hk rho hright T

theorem expected_native_residual_literal : ∀ k d : ℕ, ∀ T t : ℝ,
    nativeTruncatedResidual k d T t=
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ))-
        (∫ s : ℝ,(auxCompletionKernel k s:ℂ)*
          (((Icc (0:ℝ) T).indicator (primeFieldFamily d)) (t-s):ℂ)) := by
  intros
  rfl

theorem expected_native_terminal_memory_lower :
    ∀ k d : ℕ, 1≤k → ∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re → ∀ T : ℝ,
    Real.sqrt (2*auxCompletionAlpha k)/auxCompletionBound k*
      max (((2*((rho:ℂ)-1/2).re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
        ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
          ((zeroMult (rho:ℂ)-1).factorial:ℝ))*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
            Real.exp (((rho:ℂ)-1/2).re*T)-‖nativeAuxiliaryStableVector k d‖) 0≤
      ∫ s : ℝ in Icc 0 T,Real.exp (-auxCompletionAlpha k*(T-s))*|primeFieldFamily d s| := by
  intro k d hk rho hright T
  exact native_terminal_memory_lower k d hk rho hright T

#print axioms Zeta23.OPICAFollowup.native_auxiliary_top_moment
#print axioms Zeta23.OPICAFollowup.native_auxiliary_tail_residual_lower
#print axioms Zeta23.OPICAFollowup.native_terminal_memory_lower
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_auxiliary_top_moment
#print axioms Zeta23.OPICAFollowup.nativeAuxiliaryInput_completedPrime
#print axioms Zeta23.OPICAFollowup.nativeAuxiliaryInputLaplace_eq_continuation
#print axioms Zeta23.OPICAFollowup.Validation.expected_actual_logweighted_drive
#print axioms Zeta23.OPICAFollowup.Validation.expected_actual_auxiliary_integrand
#print axioms Zeta23.OPICAFollowup.Validation.expected_actual_auxiliary_safe_laplace
#print axioms Zeta23.OPICAFollowup.Validation.expected_actual_simple_zero_phase
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_auxiliary_tail_residual_lower
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_terminal_memory_lower

end Zeta23.OPICAFollowup.Validation
