import Zeta23.ExceptionalZero.UniversalSincPhysicalDetector
import Zeta23.CCM.OriginalSincNativeSource

/-!
# The physical and native original kernels are the same functions

The native facade keeps its definitions independent of the zero carrier.
These consuming identities compare the actual differential expressions;
no source adapter or Fourier bridge is accepted as a caller hypothesis.
-/

noncomputable section

namespace Zeta23.ExceptionalZero

theorem originalSincTest_eq_native_kernel (s : ℝ) :
    originalSincTest s = CCM.universalSincKernel s := rfl

theorem originalSincSecondTest_eq_native_kernel (s : ℝ) :
    originalSincSecondTest s = CCM.universalSincSecondKernel s := rfl

/-- The real native source casts back to the exact twice pole-killed
complex physical source. -/
theorem universalSincSecondSource_cast_eq_physical {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (CCM.universalSincSecondSource s x : ℂ) = originalSincSecondTest s x := by
  apply Complex.ext
  · simp only [CCM.universalSincSecondSource, Complex.ofReal_re]
    rfl
  · rw [Complex.ofReal_im, originalSincSecondTest_im_eq_zero hs x]

theorem nativeOriginalSource_cast_eq_physical (x : ℝ) :
    (CCM.nativeOriginalSource x : ℂ) =
      originalSincSecondTest CCM.UniversalSinc.fixedScale x :=
  universalSincSecondSource_cast_eq_physical CCM.UniversalSinc.fixedScale_pos x

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.originalSincSecondTest_eq_native_kernel
#print axioms Zeta23.ExceptionalZero.nativeOriginalSource_cast_eq_physical
