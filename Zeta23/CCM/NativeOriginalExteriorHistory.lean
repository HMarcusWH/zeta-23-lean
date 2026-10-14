import Zeta23.CCM.OriginalDetectorFourPrimeHistories
import Zeta23.CCM.NativeExteriorSourceRecord

/-!
# Original smooth detector exterior, interior and four causal prime histories

Unlike the finite retained image, this record starts with the unchanged
two-lobe smooth source f_sigma.  Its full Weil response has an
Archimedean part, two elementary poles and *four* signed prime
histories.  Neither interior response nor full-line exterior L2 is
assumed zero/finite.

The separate finite selected image and its Galerkin residual must
be compared through an actual quantitative error bridge; the present
record does not silently identify them.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace Zeta23.CCM

/-- The original (not finite) two-lobe response. -/
def originalSmoothWeilResponse (σ a : ℝ) : ℝ → ℂ :=
  nativeWeilResponse (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a)

def originalSmoothWeilLeftExterior (σ a : ℝ) : ℝ → ℂ :=
  (Iio (0 : ℝ)).indicator (originalSmoothWeilResponse σ a)

def originalSmoothWeilInteriorHistory (σ a : ℝ) : ℝ → ℂ :=
  (Icc (0 : ℝ) (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)).indicator
    (originalSmoothWeilResponse σ a)

def originalSmoothWeilRightExterior (σ a : ℝ) : ℝ → ℂ :=
  (Ioi (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)).indicator
    (originalSmoothWeilResponse σ a)

/-- Generic endpoint-safe physical split, with no assertion that the
original interior is zero. -/
private theorem nativeSource_split_Iio_Icc_Ioi (f : ℝ → ℂ) {L : ℝ}
    (hL : 0 ≤ L) (x : ℝ) :
    f x = (Iio (0 : ℝ)).indicator f x +
      (Icc (0 : ℝ) L).indicator f x +
      (Ioi L).indicator f x := by
  by_cases hx0 : x < 0
  · have hl : x ∈ Iio (0 : ℝ) := hx0
    have hm : x ∉ Icc (0 : ℝ) L := by
      intro h
      exact (not_lt_of_ge h.1) hx0
    have hr : x ∉ Ioi L := by
      intro h
      have hh : L < x := h
      linarith
    simp [Set.indicator_of_mem hl, Set.indicator_of_notMem hm,
      Set.indicator_of_notMem hr]
  · by_cases hxL : x ≤ L
    · have hl : x ∉ Iio (0 : ℝ) := hx0
      have hm : x ∈ Icc (0 : ℝ) L := ⟨le_of_not_gt hx0, hxL⟩
      have hr : x ∉ Ioi L := not_lt_of_ge hxL
      simp [Set.indicator_of_notMem hl, Set.indicator_of_mem hm,
        Set.indicator_of_notMem hr]
    · have hl : x ∉ Iio (0 : ℝ) := hx0
      have hm : x ∉ Icc (0 : ℝ) L := by
        intro h
        exact hxL h.2
      have hr : x ∈ Ioi L := lt_of_not_ge hxL
      simp [Set.indicator_of_notMem hl, Set.indicator_of_notMem hm,
        Set.indicator_of_mem hr]

theorem originalSmoothWeilResponse_reconstruction
    (σ a : ℝ) (hL : 0 ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    (x : ℝ) :
    originalSmoothWeilResponse σ a x =
      originalSmoothWeilLeftExterior σ a x +
      originalSmoothWeilInteriorHistory σ a x +
      originalSmoothWeilRightExterior σ a x :=
  nativeSource_split_Iio_Icc_Ioi _ hL x

/-- The actual original smooth response is locally square integrable
inside the aperture. This is not a global exterior claim. -/
theorem originalSmoothWeilInterior_memLp_two (σ a : ℝ) :
    MemLp (originalSmoothWeilInteriorHistory σ a) 2 volume := by
  exact nativeWeilResponse_indicator_memLp_two
    (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_contDiff σ a)
    (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_hasCompactSupport σ a)
    0 (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)

/-- The literal signed original response decomposition. -/
theorem originalSmoothWeilResponse_arch_pole_prime (σ a x : ℝ) :
    originalSmoothWeilResponse σ a x =
      nativeWeilArchResponse
          (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x +
        nativeWeilPoleResponse
          (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x -
        nativeWeilPrimeResponse
          (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x := rfl

/-- The four separate one-sided prime translates before integration,
with no dropped reflected term. -/
def originalSmoothFourPrimeHistories (σ a x : ℝ) : ℂ :=
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
           Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)))

theorem originalSmoothFourPrimeHistories_eq (σ a x : ℝ) :
    nativeWeilPrimeResponse
        (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x =
      originalSmoothFourPrimeHistories σ a x :=
  originalDetector_nativeFourPrimeHistories σ a x

/-- A source-bound original exterior record. The caller may not install
independent substitutes for its response or history. -/
structure OriginalNativeExteriorRecord (σ a : ℝ)
    (hL : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) where
  response : ℝ → ℂ
  response_eq : response = originalSmoothWeilResponse σ a
  left : ℝ → ℂ
  left_eq : left = originalSmoothWeilLeftExterior σ a
  interior : ℝ → ℂ
  interior_eq : interior = originalSmoothWeilInteriorHistory σ a
  right : ℝ → ℂ
  right_eq : right = originalSmoothWeilRightExterior σ a
  primeHistories : ℝ → ℂ
  primeHistories_eq : primeHistories = originalSmoothFourPrimeHistories σ a
  reconstruction : ∀ x, response x = left x + interior x + right x
  interior_memLp : MemLp interior 2 volume
  prime_eq : ∀ x,
    nativeWeilPrimeResponse
      (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x = primeHistories x

/-- Fully constructed on the original smooth source, independently
of a retained finite eigenvector. -/
def OriginalNativeExteriorRecord.fromOriginalSource
    (σ a : ℝ) (hL : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) :
    OriginalNativeExteriorRecord σ a hL where
  response := originalSmoothWeilResponse σ a
  response_eq := rfl
  left := originalSmoothWeilLeftExterior σ a
  left_eq := rfl
  interior := originalSmoothWeilInteriorHistory σ a
  interior_eq := rfl
  right := originalSmoothWeilRightExterior σ a
  right_eq := rfl
  primeHistories := originalSmoothFourPrimeHistories σ a
  primeHistories_eq := rfl
  reconstruction := originalSmoothWeilResponse_reconstruction σ a hL.le
  interior_memLp := originalSmoothWeilInterior_memLp_two σ a
  prime_eq := originalSmoothFourPrimeHistories_eq σ a

/-- The original physical history is not replaced by a contact: its
Archimedean, two elementary-pole and FOUR signed prime channels
reconstruct the exact full response, and the actual interior is retained. -/
theorem originalNativeExterior_history_eq
    (σ a : ℝ)
    (hL : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    (x : ℝ) :
    originalSmoothWeilResponse σ a x =
      nativeWeilArchResponse
        (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x +
      nativeWeilPoleResponse
        (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x -
      originalSmoothFourPrimeHistories σ a x ∧
    originalSmoothWeilResponse σ a x =
      originalSmoothWeilLeftExterior σ a x +
      originalSmoothWeilInteriorHistory σ a x +
      originalSmoothWeilRightExterior σ a x := by
  constructor
  · rw [originalSmoothWeilResponse_arch_pole_prime,
      originalSmoothFourPrimeHistories_eq]
  · exact originalSmoothWeilResponse_reconstruction σ a hL.le x

/-- Exact signed difference of the genuine finite native response and
the genuine original smooth source, with every Archimedean, pole and
prime channel retained. This pointwise residual is NOT the constrained
normal or outer-Galerkin residual; those are additional required output
fields and are not silently identified here. -/
theorem originalNativeExterior_residual_eq
    (σ : ReversalParity) (L : ℝ) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd)
    (a x : ℝ) :
    originalDetectorNativeResponse σ L Kd p x -
      originalSmoothWeilResponse (nativeOriginalDetectorPhaseSign σ) a x =
    (nativeWeilArchResponse
        (finitePhysicalSynthesis L Kd
          (canonicalNativeCoefficientInclusion σ L Kd p)) x -
      nativeWeilArchResponse
        (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial
          (nativeOriginalDetectorPhaseSign σ) a) x) +
    (nativeWeilPoleResponse
        (finitePhysicalSynthesis L Kd
          (canonicalNativeCoefficientInclusion σ L Kd p)) x -
      nativeWeilPoleResponse
        (Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial
          (nativeOriginalDetectorPhaseSign σ) a) x) -
    (nativeWeilPrimeResponse
        (finitePhysicalSynthesis L Kd
          (canonicalNativeCoefficientInclusion σ L Kd p)) x -
      originalSmoothFourPrimeHistories
        (nativeOriginalDetectorPhaseSign σ) a x) := by
  rw [originalDetectorNativeResponse, originalSmoothWeilResponse]
  rw [nativeWeilResponse_decomposition, nativeWeilResponse_decomposition]
  rw [← originalSmoothFourPrimeHistories_eq]
  ring


end Zeta23.CCM

#print axioms Zeta23.CCM.originalSmoothWeilResponse_reconstruction
#print axioms Zeta23.CCM.originalSmoothWeilInterior_memLp_two
#print axioms Zeta23.CCM.originalSmoothFourPrimeHistories_eq

#print axioms Zeta23.CCM.originalNativeExterior_history_eq
#print axioms Zeta23.CCM.originalNativeExterior_residual_eq
