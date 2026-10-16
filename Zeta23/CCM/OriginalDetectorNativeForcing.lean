import Zeta23.CCM.NativeWeilResponse
import Zeta23.CCM.NativeWeilResponseBounds
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

open MeasureTheory Complex Set
open scoped ComplexConjugate

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

/-- The native finite predecessor forcing is the actual adjoint-projection
of the shifted native response.  Its physical mixed pairings are fixed by
the preceding Weil-response theorem; it is not an independently supplied
free vector. -/
def originalDetectorNativeForcing (σ : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL)
    (p : nativePoleNeutralParitySpace σ L Kd) :
    nativePoleNeutralParitySpace σ L (s.cutoff - 1) :=
  (nativeDetectorPredecessorEmbedding σ s).toLinearMap.adjoint
    (nativePoleNeutralParityShifted σ L Kd (-s.eta) p)

/-- Physical mixed formula for the same original detector's projected
forcing.  It keeps the full literal response and the correct +eta term. -/
theorem originalDetectorNativeForcing_physical_mixed (σ : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (s : NativeDeepThresholdGroundData L Kd D hL)
    (p : nativePoleNeutralParitySpace σ L Kd)
    (v : nativePoleNeutralParitySpace σ L (s.cutoff - 1)) :
    inner ℂ v (originalDetectorNativeForcing σ s p) =
      (∫ x : ℝ,
        nativeWeilResponse
          (finitePhysicalSynthesis L Kd
            (canonicalNativeCoefficientInclusion σ L Kd p)) x *
        conj (finitePhysicalSynthesis L Kd
          (canonicalNativeCoefficientInclusion σ L Kd
            (nativeDetectorPredecessorEmbedding σ s v)) x)) +
      (s.eta : ℂ) * inner ℂ (nativeDetectorPredecessorEmbedding σ s v) p := by
  let J := nativeDetectorPredecessorEmbedding σ s
  let T := nativePoleNeutralParityShifted σ L Kd (-s.eta)
  have hadj : inner ℂ v (J.toLinearMap.adjoint (T p)) =
      inner ℂ (J v) (T p) := by
    simpa only [LinearIsometry.coe_toLinearMap] using
      (LinearMap.adjoint_inner_right J.toLinearMap v (T p))
  change inner ℂ v (J.toLinearMap.adjoint (T p)) = _
  exact hadj.trans (originalDetector_nativeWeil_predecessor_mixed σ s p v).symm

/-- Finite block expansion of the *actual* projected original-detector
forcing: predecessor block applied to x, plus the full orthogonal-complement
coupling B y.  The complement may have dimension Kd-cutoff+1. -/
theorem originalDetectorNativeForcing_eq_predecessor_plus_coupling
    (σ : ReversalParity) {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s)
    (p : nativePoleNeutralParitySpace σ L Kd) :
    let J := nativeDetectorPredecessorEmbedding σ s
    let T := nativePoleNeutralParityShifted σ L Kd (-s.eta)
    let x := J.toLinearMap.adjoint p
    let y := isometricDetectorComplementCoordinate J p
    originalDetectorNativeForcing σ s p =
      nativeDetectorPredecessorEquiv σ r x + isometricDetectorCoupling J T y := by
  let J := nativeDetectorPredecessorEmbedding σ s
  let T := nativePoleNeutralParityShifted σ L Kd (-s.eta)
  let x := J.toLinearMap.adjoint p
  let y := isometricDetectorComplementCoordinate J p
  have hsplit : J x + (y : nativePoleNeutralParitySpace σ L Kd) = p :=
    isometricDetector_coordinate_decomposition J p
  change J.toLinearMap.adjoint (T p) =
    nativeDetectorPredecessorEquiv σ r x + isometricDetectorCoupling J T y
  calc
    J.toLinearMap.adjoint (T p) =
        J.toLinearMap.adjoint (T (J x)) +
          J.toLinearMap.adjoint (T (y : nativePoleNeutralParitySpace σ L Kd)) := by
      rw [← hsplit, map_add, map_add]
    _ = nativeDetectorPredecessorEquiv σ r x + isometricDetectorCoupling J T y := by
      rw [← nativeDetectorPredecessorEquiv_eq_compression σ r x]
      rfl

/-- The requested source-side forcing endpoint: the actual shifted
original detector is projected by the physical Weil response, then
identified with the *same* retained full-complement Schur blocks.

The four signed histories of the SMOOTH original source and its
finite-image error are distinct downstream obligations; the finite
response below keeps its own Archimedean, pole, and both prime terms. -/
theorem originalDetector_projectedForcing_eq
    (σ : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s)
    (p : nativePoleNeutralParitySpace σ L Kd) :
    let J := nativeDetectorPredecessorEmbedding σ s
    let T := nativePoleNeutralParityShifted σ L Kd (-s.eta)
    let P := nativeDetectorPredecessorEquiv σ r
    let x := J.toLinearMap.adjoint p
    let y := isometricDetectorComplementCoordinate J p
    originalDetectorNativeForcing σ s p =
        P x + isometricDetectorCoupling J T y ∧
      ∀ v : nativePoleNeutralParitySpace σ L (s.cutoff - 1),
        inner ℂ v (originalDetectorNativeForcing σ s p) =
          (∫ z : ℝ,
            nativeWeilResponse
              (finitePhysicalSynthesis L Kd
                (canonicalNativeCoefficientInclusion σ L Kd p)) z *
              conj (finitePhysicalSynthesis L Kd
                (canonicalNativeCoefficientInclusion σ L Kd (J v)) z)) +
            (s.eta : ℂ) * inner ℂ (J v) p := by
  dsimp only
  constructor
  · exact originalDetectorNativeForcing_eq_predecessor_plus_coupling σ r p
  · intro v
    exact originalDetectorNativeForcing_physical_mixed σ s p v


/-- The actual source-independent Weil part of the native forcing
error. The constant C_Q is constructed from the fixed gamma/prime
data; only the existing true H1 and finite physical isometry bounds
are used. The separate eta term and its actual source H1 transport
remain a required next lemma. -/
theorem originalDetector_forcingWeilError_bound :
    ∃ C_Q : ℝ, 0 < C_Q ∧
      ∀ (σ : ReversalParity) (L : ℝ) (hL : 0 < L) (K : ℕ)
        (e : ℝ → ℂ) (he : ContDiff ℝ 2 e)
        (hs : tsupport e ⊆ Icc (0 : ℝ) L)
        (v : nativePoleNeutralParitySpace σ L K),
        ‖Zeta23.zetaZeroConfig.W e
          (finitePhysicalSynthesis L K
            (canonicalNativeCoefficientInclusion σ L K v))‖ ≤
        C_Q * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm e *
          (Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖) := by
  obtain ⟨C_Q, hC, hB⟩ := nativeWeilResponse_bilinear_bound
  refine ⟨C_Q, hC, ?_⟩
  intro σ L hL K e he hs v
  let f : ℝ → ℂ :=
    finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)
  have hvlegal : canonicalNativeCoefficientInclusion σ L K v ∈
      euclideanBoundaryFlatSubspace K := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L K v
  have hv : ContDiff ℝ 2 f :=
    contDiff_localizedFiniteVector_of_boundaryFlat K _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K _).mp hvlegal)
  have hvs : tsupport f ⊆ Icc (0 : ℝ) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hout
    apply hx
    change finitePhysicalSynthesis L K
      (canonicalNativeCoefficientInclusion σ L K v) x = 0
    unfold finitePhysicalSynthesis
    rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hout]
  have hW := hB L e f hL.le he hv hs hvs
  have hH := canonicalNativePhysicalSynthesis_H1_bound σ hL K v
  have hH' : nativePhysicalH1Norm f ≤
      Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖ := hH
  have hscale : 0 ≤ C_Q * (1 + L) * Real.exp (L / 2) *
        nativePhysicalH1Norm e := by
    have hc1 : 0 ≤ (1 + L : ℝ) := by linarith
    have he0 : 0 ≤ nativePhysicalH1Norm e :=
      nativePhysicalH1Norm_nonneg e
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC.le hc1) (Real.exp_pos _).le) he0
  calc
    ‖Zeta23.zetaZeroConfig.W e f‖ ≤
      C_Q * (1 + L) * Real.exp (L / 2) *
        nativePhysicalH1Norm e * nativePhysicalH1Norm f := hW
    _ ≤ C_Q * (1 + L) * Real.exp (L / 2) *
      nativePhysicalH1Norm e *
        (Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left hH' hscale


end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetector_nativeWeil_mixed
#print axioms Zeta23.CCM.originalDetector_nativeWeil_shifted_mixed
#print axioms Zeta23.CCM.originalDetector_nativeWeil_predecessor_mixed

#print axioms Zeta23.CCM.originalDetectorNativeForcing_physical_mixed
#print axioms Zeta23.CCM.originalDetectorNativeForcing_eq_predecessor_plus_coupling

#print axioms Zeta23.CCM.originalDetector_projectedForcing_eq

#print axioms Zeta23.CCM.originalDetector_forcingWeilError_bound
