import Zeta23.CCM.OriginalSincNativeConvolution
import Zeta23.CCM.NativeIntegerDriveFiniteOrderBounds
import Zeta23.CCM.NativePositiveCompletionComplexLaplace
import Zeta23.CCM.NativeCompletionEquation
import Zeta23.CCM.OriginalSincNativeMass

/-!
# Public actual-source completion identities

The multiplier, its removable value and the strict mass bound are facts
about the constructed positive kernel. Stability of its completed input
is independent of the still open damped-L2 assertion about the prime field.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.CCM

theorem native_divisor_convolution_identity (t : ℝ) :
    nativeIntegerTranslateAction nativeOriginalPrimeField t = nativeOriginalIntegerDrive t :=
  nativeIntegerTranslateAction_primeField_eq_integerDriveField nativeOriginalSource_supported t

alias nativePositiveCompletion_laplace := nativePositiveCompletion_complexLaplace

alias nativePositiveCompletion_laplace_half := nativePositiveCompletion_complexLaplace_half

alias nativePositiveCompletion_mass_lt := nativePositiveCompletion_integral_norm_lt_605_div_621

theorem nativeOriginal_complexPrimeField_eq (t : ℝ) :
    nativeComplexPrimeField (fun x => (nativeOriginalSource x : ℂ)) t =
      (nativeOriginalPrimeField t : ℂ) :=
  nativeComplexPrimeField_ofReal nativeOriginalSource_supported t

theorem nativeOriginal_complexIntegerDrive_eq (t : ℝ) :
    nativeComplexIntegerDrive (fun x => (nativeOriginalSource x : ℂ)) t =
      (nativeOriginalIntegerDrive t : ℂ) :=
  nativeComplexIntegerDrive_ofReal nativeOriginalSource_supported t

theorem nativeCompletedInput_undamped_memLp :
    MemLp (nativeDampedCompletedInput 0) 2 volume :=
  nativeCompletedInput_memLp le_rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.native_divisor_convolution_identity
#print axioms Zeta23.CCM.nativePositiveCompletion_laplace
#print axioms Zeta23.CCM.nativePositiveCompletion_laplace_half
#print axioms Zeta23.CCM.nativePositiveCompletion_mass_lt
#print axioms Zeta23.CCM.nativeOriginal_complexPrimeField_eq
#print axioms Zeta23.CCM.nativeOriginal_complexIntegerDrive_eq
#print axioms Zeta23.CCM.nativeCompletedInput_undamped_memLp
