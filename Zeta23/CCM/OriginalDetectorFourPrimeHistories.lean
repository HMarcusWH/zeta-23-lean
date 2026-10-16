import Zeta23.CCM.OriginalDetectorNativeForcing
import Zeta23.CCM.OriginalSincNativeConvolution
import Zeta23.CCM.OriginalDetectorOriginalPhaseL1Bounds

/-!
# Four separate original prime histories

The full Weil-prime response has both translations. For a reflected
two-lobe detector, the original even kernel converts them to four
one-sided prime fields. This is a signed identity on the literal
physical detector, not an absolute-value estimate or a ground-state
substitution. No global L2 assumption about any prime field occurs.
-/

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace Zeta23.CCM

/-- The four-history identity for any compact, even complex kernel on
the native one-sided prime lattice. The four shifted fields remain
separate; no cancellation or positivity is presumed. -/
theorem nativeWeilPrimeResponse_twoLobe_fourHistories
    {s : ℝ} {k : ℝ → ℂ}
    (hks : NativeComplexSourceSupported s k)
    (hkEven : Function.Even k)
    (κ σ : ℂ) (c L x : ℝ) :
    nativeWeilPrimeResponse
      (fun t : ℝ => κ * (k (t - c) + σ * k (L - t - c))) x =
      κ * ((nativeComplexPrimeField k (x - c) +
            nativeComplexPrimeField k (c - x)) +
           σ * (nativeComplexPrimeField k (L - x - c) +
            nativeComplexPrimeField k (x + c - L))) := by
  let A : ℕ → ℂ := fun n =>
    (nativePrimeCoefficient n : ℂ) * k (x - c - Real.log n)
  let B : ℕ → ℂ := fun n =>
    (nativePrimeCoefficient n : ℂ) * k (c - x - Real.log n)
  let C : ℕ → ℂ := fun n =>
    (nativePrimeCoefficient n : ℂ) * k (L - x - c - Real.log n)
  let D : ℕ → ℂ := fun n =>
    (nativePrimeCoefficient n : ℂ) * k (x + c - L - Real.log n)
  have hA : Summable A := nativeComplexPrimeField_summable hks
  have hB : Summable B := nativeComplexPrimeField_summable hks
  have hC : Summable C := nativeComplexPrimeField_summable hks
  have hD : Summable D := nativeComplexPrimeField_summable hks
  have hAB : Summable (fun n => A n + B n) := hA.add hB
  have hCD : Summable (fun n => C n + D n) := hC.add hD
  have hCDs : Summable (fun n => σ * (C n + D n)) := hCD.mul_left σ
  have hentry (n : ℕ) :
      (nativePrimeCoefficient n : ℂ) *
        (κ * (k (x - Real.log n - c) + σ * k (L - (x - Real.log n) - c)) +
         κ * (k (x + Real.log n - c) + σ * k (L - (x + Real.log n) - c))) =
       κ * ((A n + B n) + σ * (C n + D n)) := by
    have hargB : x + Real.log n - c = -(c - x - Real.log n) := by ring
    have hargD : L - (x - Real.log n) - c = -(x + c - L - Real.log n) := by ring
    have hargA : x - Real.log n - c = x - c - Real.log n := by ring
    have hargC : L - (x + Real.log n) - c = L - x - c - Real.log n := by ring
    rw [hargB, hkEven, hargD, hkEven, hargA, hargC]
    dsimp [A, B, C, D]
    ring
  calc
    nativeWeilPrimeResponse
        (fun t : ℝ => κ * (k (t - c) + σ * k (L - t - c))) x =
      ∑' n : ℕ, κ * ((A n + B n) + σ * (C n + D n)) := by
        unfold nativeWeilPrimeResponse
        apply tsum_congr
        exact hentry
    _ = κ * ((∑' n, (A n + B n)) +
        σ * (∑' n, (C n + D n))) := by
        rw [tsum_mul_left, hAB.tsum_add hCDs, tsum_mul_left]
    _ = κ * (((∑' n, A n) + (∑' n, B n)) +
         σ * ((∑' n, C n) + (∑' n, D n))) := by
         rw [hA.tsum_add hB, hC.tsum_add hD]
    _ = _ := rfl

/-- The four histories for the *frozen* original two-lobe sinc-product
detector. The fixed lobe centre and physical normalization are retained. -/
theorem originalDetector_nativeFourPrimeHistories (σ a x : ℝ) :
    nativeWeilPrimeResponse (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x =
      (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
        ((nativeOriginalKernelPrimeField
            (x - Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter) +
          nativeOriginalKernelPrimeField
            (Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter - x)) +
         (σ : ℂ) *
          (nativeOriginalKernelPrimeField
            (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a - x -
              Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter) +
           nativeOriginalKernelPrimeField
            (x + Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter -
              Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a))) := by
  let k := Zeta23.ExceptionalZero.fixedOriginalSincKernel
  have hks : NativeComplexSourceSupported UniversalSinc.fixedScale k := by
    change tsupport (universalSincKernel UniversalSinc.fixedScale) ⊆
      Set.Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
    exact universalSincKernel_support UniversalSinc.fixedScale_pos
  have hkeven : Function.Even k :=
    Zeta23.ExceptionalZero.originalSincTest_even UniversalSinc.fixedScale_pos
  have htrial :
      Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a =
        fun t : ℝ =>
          (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
            (k (t - Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter) +
             (σ : ℂ) * k (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a -
               t - Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter)) := by
      funext t
      exact Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_reflected_formula σ a t
  rw [htrial]
  exact nativeWeilPrimeResponse_twoLobe_fourHistories hks hkeven
    (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) (σ : ℂ)
    Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
    (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) x

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeWeilPrimeResponse_twoLobe_fourHistories
#print axioms Zeta23.CCM.originalDetector_nativeFourPrimeHistories
