import Zeta23.CCM.NativeWeilResponse
import Zeta23.CCM.CanonicalPhysicalTrialRealization
import Zeta23.CCM.DetectorRetainedSchurState

/-!
# First original-detector physical forcing bridge

The actual full Weil response, including Archimedean, both pole and both
prime-translation channels, is tested against the actual native finite
physical synthesis.  No replacement ground state, formal response oracle,
or global L2 assumption about the full response is introduced.

This is the initial mixed-pairing component of T11; it does NOT yet
establish the four explicit original histories or the final H1 error.
-/

noncomputable section

open MeasureTheory Complex

namespace Zeta23.CCM

/-- The actual physical Weil response, paired with an actual finite native
test, equals the finite canonical native operator on the *same* detector.
The first argument is linear, the second conjugate-linear. -/
theorem originalDetector_nativeWeil_mixed (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (Kd : ℕ)
    (p v : nativePoleNeutralParitySpace σ L Kd) :
    (∫ x : ℝ,
      nativeWeilResponse
        (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) x *
      conj (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd v) x)) =
      inner ℂ v (nativePoleNeutralParityCanonical σ L Kd p) := by
  have hpLegal :
      canonicalNativeCoefficientInclusion σ L Kd p ∈
        euclideanBoundaryFlatSubspace Kd := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L Kd p
  have hvLegal :
      canonicalNativeCoefficientInclusion σ L Kd v ∈
        euclideanBoundaryFlatSubspace Kd := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L Kd v
  have hpC : ContDiff ℝ 2
      (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) :=
    contDiff_localizedFiniteVector_of_boundaryFlat Kd _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat Kd _).mp hpLegal)
  have hvC : ContDiff ℝ 2
      (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd v)) :=
    contDiff_localizedFiniteVector_of_boundaryFlat Kd _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat Kd _).mp hvLegal)
  have hpS : HasCompactSupport
      (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) :=
    localizedFiniteVector_hasCompactSupport L Kd _
  have hvS : HasCompactSupport
      (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd v)) :=
    localizedFiniteVector_hasCompactSupport L Kd _
  exact (nativeWeilResponse_pairing hpC hpS hvC.continuous hvS).symm.trans
    (canonicalNativePhysicalSynthesis_mixed_Weil σ hL Kd p v)

/-- The correct original-detector shift is minus eta: thus the physical
forcing includes +eta times the *same* detector.  Do not substitute the
selected ground's separate negative eigenvalue shift. -/
theorem originalDetector_nativeWeil_shifted_mixed (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (Kd : ℕ) (η : ℝ)
    (p v : nativePoleNeutralParitySpace σ L Kd) :
    (∫ x : ℝ,
      nativeWeilResponse
        (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) x *
      conj (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd v) x)) +
      (η : ℂ) * inner ℂ v p =
      inner ℂ v (nativePoleNeutralParityShifted σ L Kd (-η) p) := by
  rw [originalDetector_nativeWeil_mixed σ hL Kd p v]
  simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right, inner_smul_right]
  push_cast
  ring

/-- Physical response is tested on the actual stored predecessor embedding.
The complement at Kd has its full dimension, not a selected-ground shell. -/
theorem originalDetector_nativeWeil_predecessor_mixed
    (σ : ReversalParity) {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL)
    (p : nativePoleNeutralParitySpace σ L Kd)
    (v : nativePoleNeutralParitySpace σ L (s.cutoff - 1)) :
    (∫ x : ℝ,
      nativeWeilResponse
        (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p)) x *
      conj (finitePhysicalSynthesis L Kd
        (canonicalNativeCoefficientInclusion σ L Kd
          (nativeDetectorPredecessorEmbedding σ s v)) x)) +
      (s.eta : ℂ) * inner ℂ (nativeDetectorPredecessorEmbedding σ s v) p =
      inner ℂ (nativeDetectorPredecessorEmbedding σ s v)
        (nativePoleNeutralParityShifted σ L Kd (-s.eta) p) :=
  originalDetector_nativeWeil_shifted_mixed σ hL Kd s.eta p
    (nativeDetectorPredecessorEmbedding σ s v)

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetector_nativeWeil_mixed
#print axioms Zeta23.CCM.originalDetector_nativeWeil_shifted_mixed
#print axioms Zeta23.CCM.originalDetector_nativeWeil_predecessor_mixed
