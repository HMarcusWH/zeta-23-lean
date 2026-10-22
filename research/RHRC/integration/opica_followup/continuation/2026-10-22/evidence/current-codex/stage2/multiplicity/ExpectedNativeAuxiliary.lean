import Zeta23.OPICAFollowup.MultiplicityTail

/-! Independent Stage2 consumers of the actual MultiplicityTail module.
The stated types expand the physical convolution, residual and memory. -/
noncomputable section
open Set MeasureTheory Filter
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.CCM Zeta23.ExceptionalZero

def expected_native_auxiliary_top_moment :
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
  simpa only [nativeAuxiliaryInput,nativeAuxiliaryMoment] using native_auxiliary_top_moment k d rho hright

def expected_actual_auxiliary_factorial_stability : ∀ k d : ℕ,
    ‖nativeAuxiliaryStableVector k d‖≤
      (2/(Nat.factorial (k+1):ℝ))*‖auxiliaryDriveCausalVector d‖ :=
  nativeAuxiliaryStableVector_factorial_bound

def expected_actual_logweighted_drive : ∀ d : ℕ, ∀ t : ℝ,
    integerDriveFamily d t=
      ∑' n : ℕ,(Real.log n/Real.sqrt n)*sourceOrderFamily d (t-Real.log n) := by
  intro d t
  rfl

def expected_actual_auxiliary_integrand : ∀ k d : ℕ, ∀ t : ℝ,
    Integrable (fun s : ℝ => (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) :=
  nativeAuxiliaryInput_integrand_integrable

def expected_actual_auxiliary_safe_laplace : ∀ k d : ℕ, ∀ z : ℂ, 1/2<z.re →
    (∫ t : ℝ,Complex.exp (-z*(t:ℂ))*(∫ s : ℝ,
      (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
      -auxRationalFactor k z*sourceFamilyLaplace d z*deriv riemannZeta (z+1/2) := by
  intro k d z hz
  exact (nativeAuxiliaryInput_initial_laplace k d hz).2

def expected_actual_simple_zero_phase : ∀ k d : ℕ, ∀ rho : zetaZeroConfig.carrier,
    1/2<(rho:ℂ).re → zeroMult (rho:ℂ)=1 →
    (∫ t : ℝ,Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
        -auxRationalFactor k ((rho:ℂ)-1/2)*sourceFamilyLaplace d ((rho:ℂ)-1/2)*
          deriv riemannZeta (rho:ℂ) := by
  intro k d rho hright hm
  have h := nativeAuxiliaryMoment_top_value k d rho hright
  simpa only [hm,Nat.sub_self,nativeAuxiliaryMoment,nativeAuxiliaryInput,pow_zero,
    pow_one,one_mul,neg_mul,iteratedDeriv_one] using h

def expected_native_auxiliary_tail_residual_lower :
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

def expected_native_residual_literal : ∀ k d : ℕ, ∀ T t : ℝ,
    nativeTruncatedResidual k d T t=
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ))-
        (∫ s : ℝ,(auxCompletionKernel k s:ℂ)*
          (((Icc (0:ℝ) T).indicator (primeFieldFamily d)) (t-s):ℂ)) := by
  intros
  rfl

def expected_native_terminal_memory_lower :
    ∀ k d : ℕ, 1≤k → ∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re → ∀ T : ℝ,
    Real.sqrt (2*auxCompletionAlpha k)/auxCompletionBound k*
      max (((2*((rho:ℂ)-1/2).re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
        ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
          ((zeroMult (rho:ℂ)-1).factorial:ℝ))*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
            Real.exp (((rho:ℂ)-1/2).re*T)-‖nativeAuxiliaryStableVector k d‖) 0≤
      ∫ s : ℝ in Icc 0 T,Real.exp (-auxCompletionAlpha k*(T-s))*|primeFieldFamily d s| := by
  intro k d hk rho hright T
  exact native_terminal_memory_lower k d hk rho hright T

#print axioms native_auxiliary_top_moment
#print axioms expected_native_auxiliary_top_moment
#print axioms nativeAuxiliaryInput_completedPrime
#print axioms nativeAuxiliaryInputLaplace_eq_continuation
#print axioms expected_actual_logweighted_drive
#print axioms expected_actual_auxiliary_integrand
#print axioms expected_actual_auxiliary_safe_laplace
#print axioms expected_actual_simple_zero_phase
#print axioms expected_native_auxiliary_tail_residual_lower
#print axioms expected_native_terminal_memory_lower

end Zeta23.OPICAFollowup.Validation
