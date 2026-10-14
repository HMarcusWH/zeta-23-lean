import Zeta23.CCM.NativeSelectedGroundSchur

noncomputable section

namespace Zeta23.CCM

open Matrix

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The finite retained state is constructed from the actual supplied native
parity detector. Its original parity, vector, normalization and depth stay
separate from the selected ground, its parity, cutoff and actual lam.
Both Schur operators and their different inverse budgets are constructed
from this state. Source generation and finite-approximation production are
upstream obligations; no source or phase facts are assigned to the ground.
-/

def nativePoleNeutralParityAmbient (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) : EuclideanSpace ℂ (Fin (2 * K + 1)) := by
  cases sigma
  · exact p.val.val
  · exact p.val.val

theorem nativePoleNeutralParityAmbient_norm (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    ‖nativePoleNeutralParityAmbient sigma L K p‖ = ‖p‖ := by
  cases sigma <;> rfl

theorem nativePoleNeutralParityAmbient_legal (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    nativePoleNeutralParityAmbient sigma L K p ∈ euclideanBoundaryFlatSubspace K := by
  apply (mem_euclideanBoundaryFlatSubspace_iff K _).mpr
  cases sigma
  · exact ((mem_euclideanEvenBoundaryFlatSubspace_iff K p.val.val).mp p.val.property).1
  · exact ((mem_euclideanOddBoundaryFlatSubspace_iff K p.val.val).mp p.val.property).1

theorem nativePoleNeutralParityAmbient_poles (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    canonicalPoleEvenFunctional L K (nativePoleNeutralParityAmbient sigma L K p) = 0 ∧
      canonicalPoleOddFunctional L K (nativePoleNeutralParityAmbient sigma L K p) = 0 := by
  cases sigma
  · constructor
    · exact (mem_poleNeutralEvenSubspace L K p.val).mp p.property
    · change poleOddProfile L K ⬝ᵥ evenBoundaryFlatRawCoefficients K p.val = 0
      exact poleOddProfile_dot_evenBoundaryFlat_eq_zero L K p.val
  · constructor
    · let raw := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) p.val.val
      have hraw := (mem_euclideanOddBoundaryFlatSubspace_iff K p.val.val).mp p.val.property
      have hrev : reverseCoefficients K raw = -raw :=
        (mem_oddCoefficientSubspace_iff K raw).mp hraw.2
      change poleEvenProfile L K ⬝ᵥ raw = 0
      rw [dotProduct_comm]
      exact dotProduct_eq_zero_of_reverse_odd_even K raw (poleEvenProfile L K)
        hrev (reverseCoefficients_poleEvenProfile L K)
    · exact (mem_poleNeutralOddSubspace L K p.val).mp p.property

theorem nativePoleNeutralParityAmbient_energy (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin (nativePoleNeutralParityAmbient sigma L K p))
        (nativePoleNeutralParityAmbient sigma L K p) =
      inner ℂ (nativePoleNeutralParityCanonical sigma L K p) p := by
  cases sigma
  · exact (inner_poleNeutralEvenCompressedCanonical_self L K p).symm
  · exact (inner_poleNeutralOddCompressedCanonical_self L K p).symm

structure DetectorRetainedSchurState (sigma : ReversalParity) (L : ℝ) (Kd : ℕ) (D : ℝ)
    (hL : 0 < L) where
  detector : nativePoleNeutralParitySpace sigma L Kd
  detector_unit : ‖detector‖ = 1
  detector_depth : (inner ℂ (nativePoleNeutralParityCanonical sigma L Kd detector) detector).re ≤ -D
  depth_pos : 0 < D
  selection : NativeDeepThresholdGroundData L Kd D hL
  inverses : NativeDeepThresholdInverseData selection
  selectedParity : ReversalParity
  selectedGround : nativePoleNeutralParitySpace selectedParity L selection.cutoff
  selectedGround_unit : ‖selectedGround‖ = 1
  selectedGround_eigen : nativePoleNeutralParityCanonical selectedParity L selection.cutoff selectedGround =
    (selection.lam : ℂ) • selectedGround

/-- Construct the finite retained packet from the original supplied native
unit detector, with no selected ground, inverse or Schur identity premise. -/
theorem exists_detectorRetainedSchurState_of_original_native_trial
    (sigma : ReversalParity) {L : ℝ} (hL : 0 < L) (Kd : ℕ) (hKd : 3 ≤ Kd)
    (D : ℝ) (hD : 0 < D) (p : nativePoleNeutralParitySpace sigma L Kd) (hpUnit : ‖p‖ = 1)
    (hpDepth : (inner ℂ (nativePoleNeutralParityCanonical sigma L Kd p) p).re ≤ -D) :
    ∃ state : DetectorRetainedSchurState sigma L Kd D hL, state.detector = p := by
  let pa := nativePoleNeutralParityAmbient sigma L Kd p
  have hlegal : pa ∈ euclideanBoundaryFlatSubspace Kd := nativePoleNeutralParityAmbient_legal sigma L Kd p
  obtain ⟨hpEven, hpOdd⟩ := nativePoleNeutralParityAmbient_poles sigma L Kd p
  have hunit : ‖pa‖ = 1 := (nativePoleNeutralParityAmbient_norm sigma L Kd p).trans hpUnit
  have hdepth : (inner ℂ ((canonicalSourceMatrix L Kd).toEuclideanLin pa) pa).re ≤ -D := by
    rw [nativePoleNeutralParityAmbient_energy]
    exact hpDepth
  obtain ⟨s⟩ := exists_nativeDeepThresholdGround_of_given_trial hL Kd hKd D hD
    pa hlegal hpEven hpOdd hunit hdepth
  let r := nativeDeepThresholdInverseData hD s
  rcases s.unit_actual_ground with ⟨u, huUnit, huEigen⟩ | ⟨w, hwUnit, hwEigen⟩
  · refine ⟨{
      detector := p
      detector_unit := hpUnit
      detector_depth := hpDepth
      depth_pos := hD
      selection := s
      inverses := r
      selectedParity := .even
      selectedGround := u
      selectedGround_unit := huUnit
      selectedGround_eigen := huEigen }, rfl⟩
  · refine ⟨{
      detector := p
      detector_unit := hpUnit
      detector_depth := hpDepth
      depth_pos := hD
      selection := s
      inverses := r
      selectedParity := .odd
      selectedGround := w
      selectedGround_unit := hwUnit
      selectedGround_eigen := hwEigen }, rfl⟩

/-- The full original detector complement carries the retained negative
depth, independently of the separately stored selected ground. -/
theorem originalDetector_schur_loss_lower {sigma : ReversalParity} {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (state : DetectorRetainedSchurState sigma L Kd D hL) :
    let y := isometricDetectorComplementCoordinate
      (nativeDetectorPredecessorEmbedding sigma state.selection) state.detector
    y ≠ 0 ∧ (inner ℂ (nativeDetectorSchurOperator sigma state.inverses y) y).re ≤ -(D - state.selection.eta) ∧
      (inner ℂ (nativeDetectorSchurOperator sigma state.inverses y) y).re < -D / 2 :=
  nativeDetectorSchur_original_depth sigma state.depth_pos state.inverses
    state.detector state.detector_unit state.detector_depth

theorem originalDetector_schur_completion {sigma : ReversalParity} {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (state : DetectorRetainedSchurState sigma L Kd D hL) :
    let J := nativeDetectorPredecessorEmbedding sigma state.selection
    let T := nativePoleNeutralParityShifted sigma L Kd (-state.selection.eta)
    let P := nativeDetectorPredecessorEquiv sigma state.inverses
    let x := J.toLinearMap.adjoint state.detector
    let y := isometricDetectorComplementCoordinate J state.detector
    let z := x + isometricDetectorResponse J T P y
    inner ℂ (T state.detector) state.detector =
      inner ℂ (P z) z + inner ℂ (nativeDetectorSchurOperator sigma state.inverses y) y :=
  nativeDetectorSchur_completedSquare sigma state.inverses state.detector

theorem selectedGround_shiftedSchur_eq {sigma : ReversalParity} {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (state : DetectorRetainedSchurState sigma L Kd D hL) :
    let gamma := state.selectedParity
    let J := nativeSelectedGroundPredecessorEmbedding gamma state.selection
    let T := nativePoleNeutralParityShifted gamma L state.selection.cutoff state.selection.lam
    let P := nativeSelectedGroundPredecessorEquiv gamma state.inverses
    let y := isometricDetectorComplementCoordinate J state.selectedGround
    let response := isometricDetectorResponse J T P y
    inner ℂ (nativePoleNeutralParityCanonical gamma L state.selection.cutoff
        (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff))
        (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff) -
      (state.selection.lam : ℂ) * inner ℂ (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff)
        (y : nativePoleNeutralParitySpace gamma L state.selection.cutoff) =
      inner ℂ (P response) response := by
  have hu0 : state.selectedGround ≠ 0 := by
    intro hz
    have huUnit := state.selectedGround_unit
    rw [hz, norm_zero] at huUnit
    norm_num at huUnit
  exact nativeSelectedGround_shiftedSchur_eq state.selectedParity state.inverses
    state.selectedGround hu0 state.selectedGround_eigen

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleNeutralParityAmbient_poles
#print axioms Zeta23.CCM.nativePoleNeutralParityAmbient_energy
#print axioms Zeta23.CCM.exists_detectorRetainedSchurState_of_original_native_trial
#print axioms Zeta23.CCM.originalDetector_schur_loss_lower
#print axioms Zeta23.CCM.originalDetector_schur_completion
#print axioms Zeta23.CCM.selectedGround_shiftedSchur_eq
