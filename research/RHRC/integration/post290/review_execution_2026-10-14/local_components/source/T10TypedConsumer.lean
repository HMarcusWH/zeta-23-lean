import Zeta23.CCM.CanonicalPhysicalTrialRealization
import Zeta23.CCM.OriginalDetectorPaddedFinitePhysicalUnitBridge
import Zeta23.CCM.OriginalDetectorPaddedRetainedSelection

noncomputable section
open Set Complex MeasureTheory
open Zeta23.CCM Zeta23.ExceptionalZero
open scoped ComplexConjugate

example {L : ℝ} (hL : 0 < L) (K : ℕ) :
    EuclideanSpace ℂ (Fin (2 * K + 1)) →ₗᵢ[ℂ] CanonicalPhysicalL2 :=
  canonicalPhysicalIsometry hL K

example (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    canonicalNativePhysicalProjection σ hL K =
      (canonicalNativePhysicalIsometry σ hL K).toContinuousLinearMap.adjoint := rfl

example (σ : ReversalParity) {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL)
    (v : nativePoleNeutralParitySpace σ L (s.cutoff - 1)) :
    canonicalNativePhysicalIsometry σ hL Kd (nativeDetectorPredecessorEmbedding σ s v) =
      canonicalNativePhysicalIsometry σ hL (s.cutoff - 1) v :=
  canonicalNativePhysicalIsometry_predecessor σ s v

example (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : nativePoleNeutralParitySpace σ L K) (g : CanonicalPhysicalL2) :
    inner ℂ v (canonicalNativePhysicalProjection σ hL K g) =
      ∫ x : ℝ, conj (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v) x) * g x :=
  canonicalNativePhysicalProjection_inner σ hL K v g

example (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (g : CanonicalPhysicalL2) :
    canonicalNativePhysicalProjection σ hL 2 g = 0 :=
  canonicalNativePhysicalProjection_firstCutoff_zero σ hL g

example (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u v : nativePoleNeutralParitySpace σ L K) :
    Zeta23.zetaZeroConfig.W
      (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K u))
      (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)) =
      inner ℂ v (nativePoleNeutralParityCanonical σ L K u) :=
  canonicalNativePhysicalSynthesis_mixed_Weil σ hL K u v

example (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : nativePoleNeutralParitySpace σ L K) :
    originalDetectorPhysicalH1Error
      (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)) 0 ≤
      Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖ :=
  canonicalNativePhysicalSynthesis_H1_bound σ hL K v

example (σ : ReversalParity) (a : ℝ) (hL2 : 2 ≤ fixedOriginalSincTrialAperture a)
    (hL : 0 < fixedOriginalSincTrialAperture a) :
    canonicalNativePhysicalIsometry σ hL (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      (nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter hL2) =ᵐ[volume]
        originalDetectorPaddedFinitePhysicalUnit (nativeOriginalDetectorPhaseSign σ) a hL := by
  have he := canonicalNativePhysicalIsometry_ae σ hL _
    (nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter hL2)
  have hc : canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a) _
      (nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter hL2) =
      originalDetectorPaddedFinitePhaseUnitVector (nativeOriginalDetectorPhaseSign σ)
        (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hL := by
    cases σ <;> rfl
  rw [hc] at he
  have hb : originalDetectorPaddedFinitePhysicalUnit (nativeOriginalDetectorPhaseSign σ) a hL =
      finitePhysicalSynthesis (fixedOriginalSincTrialAperture a) _
        (originalDetectorPaddedFinitePhaseUnitVector (nativeOriginalDetectorPhaseSign σ)
          (fixedOriginalSincTrialAperture a) fixedOriginalSincLobeCenter hL) := by
    simpa only [finitePhysicalSynthesis] using
      originalDetectorPaddedFinitePhysicalUnit_eq_native_image (nativeOriginalDetectorPhaseSign σ) a hL
  exact he.trans (Filter.Eventually.of_forall (fun x => congrFun hb.symm x))

#print axioms Zeta23.CCM.canonicalNativePhysicalSynthesis_mixed_Weil
#print axioms Zeta23.CCM.canonicalNativePhysicalProjection_firstCutoff_zero
#print axioms Zeta23.CCM.canonicalNativePhysicalIsometry_predecessor
#print axioms Zeta23.CCM.canonicalNativePhysicalSynthesis_H1_bound

