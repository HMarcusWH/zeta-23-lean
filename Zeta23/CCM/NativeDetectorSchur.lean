import Zeta23.CCM.IsometricDetectorSchur
import Zeta23.CCM.NativeDeepThresholdInverseBudgets

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The detector Schur operator uses the original detector's own native parity
space at Kd. Its predecessor is centered extension from the selected
cutoff minus one, and its complement is the entire orthogonal complement
at Kd. The detector shift is -eta, independently of the selected lam.
The parity-indexed definitions below reduce to the unchanged actual even
and odd spaces, operators, isometries and detector inverses.
-/

def nativePoleNeutralParitySpace (sigma : ReversalParity) (L : ℝ) (K : ℕ) : Type :=
  match sigma with
  | .even => poleNeutralEvenSubspace L K
  | .odd => poleNeutralOddSubspace L K

instance nativePoleNeutralParitySpace_normedAddCommGroup (sigma : ReversalParity) (L : ℝ) (K : ℕ) :
    NormedAddCommGroup (nativePoleNeutralParitySpace sigma L K) := by
  cases sigma <;> exact inferInstance

instance nativePoleNeutralParitySpace_innerProductSpace (sigma : ReversalParity) (L : ℝ) (K : ℕ) :
    InnerProductSpace ℂ (nativePoleNeutralParitySpace sigma L K) := by
  cases sigma
  · exact poleNeutralEven_innerProductSpace L K
  · exact poleNeutralOdd_innerProductSpace L K

instance nativePoleNeutralParitySpace_finiteDimensional (sigma : ReversalParity) (L : ℝ) (K : ℕ) :
    FiniteDimensional ℂ (nativePoleNeutralParitySpace sigma L K) := by
  cases sigma <;> exact inferInstance

theorem finrank_nativePoleNeutralParitySpace (sigma : ReversalParity) {L : ℝ}
    (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K) :
    Module.finrank ℂ (nativePoleNeutralParitySpace sigma L K) = K - 2 := by
  cases sigma
  · exact finrank_poleNeutralEvenSubspace hL K hK
  · exact finrank_poleNeutralOddSubspace hL K hK

def nativePoleNeutralParityCanonical (sigma : ReversalParity) (L : ℝ) (K : ℕ) :
    nativePoleNeutralParitySpace sigma L K →ₗ[ℂ] nativePoleNeutralParitySpace sigma L K := by
  cases sigma
  · exact poleNeutralEvenCompressedCanonical L K
  · exact poleNeutralOddCompressedCanonical L K

def nativePoleNeutralParityShifted (sigma : ReversalParity) (L : ℝ) (K : ℕ) (shift : ℝ) :
    nativePoleNeutralParitySpace sigma L K →ₗ[ℂ] nativePoleNeutralParitySpace sigma L K :=
  nativePoleNeutralParityCanonical sigma L K - (shift : ℂ) • LinearMap.id

def nativePoleNeutralParityCenteredZeroExtend (sigma : ReversalParity) (L : ℝ)
    {N M : ℕ} (hNM : N ≤ M) :
    nativePoleNeutralParitySpace sigma L N →ₗᵢ[ℂ] nativePoleNeutralParitySpace sigma L M := by
  cases sigma
  · exact poleNeutralEvenCenteredZeroExtend L hNM
  · exact poleNeutralOddCenteredZeroExtend L hNM

theorem nativePoleNeutralParity_predecessor_compression_eq (sigma : ReversalParity)
    {L : ℝ} (hL : 0 < L) {N M : ℕ} (hNM : N ≤ M) :
    (nativePoleNeutralParityCenteredZeroExtend sigma L hNM).toLinearMap.adjoint.comp
      ((nativePoleNeutralParityCanonical sigma L M).comp
        (nativePoleNeutralParityCenteredZeroExtend sigma L hNM).toLinearMap) =
      nativePoleNeutralParityCanonical sigma L N := by
  cases sigma
  · exact poleNeutralEven_predecessor_compression_eq hL hNM
  · exact poleNeutralOdd_predecessor_compression_eq hL hNM

theorem nativePoleNeutralParityShifted_isSymmetric (sigma : ReversalParity)
    (L : ℝ) (K : ℕ) (shift : ℝ) :
    (nativePoleNeutralParityShifted sigma L K shift).IsSymmetric := by
  have hA : (nativePoleNeutralParityCanonical sigma L K).IsSymmetric := by
    cases sigma
    · exact poleNeutralEvenCompressedCanonical_isSymmetric L K
    · exact poleNeutralOddCompressedCanonical_isSymmetric L K
  intro u v
  simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hA u v]

def nativeDetectorPredecessorEquiv (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) :
    nativePoleNeutralParitySpace sigma L (s.cutoff - 1) ≃ₗ[ℂ]
      nativePoleNeutralParitySpace sigma L (s.cutoff - 1) := by
  cases sigma
  · exact r.evenDetector
  · exact r.oddDetector

theorem nativeDetectorPredecessorEquiv_actual (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) (v : nativePoleNeutralParitySpace sigma L (s.cutoff - 1)) :
    nativeDetectorPredecessorEquiv sigma r v =
      nativePoleNeutralParityShifted sigma L (s.cutoff - 1) (-s.eta) v := by
  cases sigma
  · exact r.evenDetector_actual v
  · exact r.oddDetector_actual v

theorem nativeDetectorPredecessorEquiv_inverse_bound (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) :
    ‖(nativeDetectorPredecessorEquiv sigma r).symm.toLinearMap.toContinuousLinearMap‖ ≤
      12 * ((Kd - 1 : ℕ) : ℝ) / D := by
  cases sigma
  · exact r.evenDetector_inverse_bound
  · exact r.oddDetector_inverse_bound

def nativeDetectorPredecessorEmbedding (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) :
    nativePoleNeutralParitySpace sigma L (s.cutoff - 1) →ₗᵢ[ℂ]
      nativePoleNeutralParitySpace sigma L Kd :=
  nativePoleNeutralParityCenteredZeroExtend sigma L
    ((Nat.sub_le s.cutoff 1).trans s.cutoff_le_detector)

def nativeDetectorComplement (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) :
    Submodule ℂ (nativePoleNeutralParitySpace sigma L Kd) :=
  isometricDetectorComplement (nativeDetectorPredecessorEmbedding sigma s)

/-- The detector complement has its full actual dimension; it is a
single shell only when the detector cutoff equals the selected cutoff. -/
theorem nativeDetectorComplement_finrank (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) :
    Module.finrank ℂ (nativeDetectorComplement sigma s) = Kd - s.cutoff + 1 := by
  let J := nativeDetectorPredecessorEmbedding sigma s
  have hprev : 2 ≤ s.cutoff - 1 := by have hK := s.cutoff_nonempty; omega
  have hKd : 2 ≤ Kd := by have hK := s.cutoff_nonempty; have hle := s.cutoff_le_detector; omega
  have hs : Module.finrank ℂ (LinearMap.range J.toLinearMap) +
      Module.finrank ℂ (nativeDetectorComplement sigma s) =
      Module.finrank ℂ (nativePoleNeutralParitySpace sigma L Kd) :=
    Submodule.finrank_add_finrank_orthogonal (LinearMap.range J.toLinearMap)
  have hr := LinearMap.finrank_range_of_inj (f := J.toLinearMap) J.injective
  rw [hr, finrank_nativePoleNeutralParitySpace sigma hL (s.cutoff - 1) hprev,
    finrank_nativePoleNeutralParitySpace sigma hL Kd hKd] at hs
  have hle := s.cutoff_le_detector
  omega

/-- The literal detector-complement operator at the detector shift. -/
def nativeDetectorSchurOperator (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) :
    nativeDetectorComplement sigma s →ₗ[ℂ] nativeDetectorComplement sigma s :=
  isometricDetectorSchurOperator (nativeDetectorPredecessorEmbedding sigma s)
    (nativePoleNeutralParityShifted sigma L Kd (-s.eta)) (nativeDetectorPredecessorEquiv sigma r)

/-- The off-diagonal detector coupling is that of the actual unshifted
canonical form: the scalar detector shift vanishes on this complement. -/
theorem nativeDetectorCoupling_shift_eq_unshifted (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (y : nativeDetectorComplement sigma s) :
    isometricDetectorCoupling (nativeDetectorPredecessorEmbedding sigma s)
        (nativePoleNeutralParityShifted sigma L Kd (-s.eta)) y =
      (nativeDetectorPredecessorEmbedding sigma s).toLinearMap.adjoint
        (nativePoleNeutralParityCanonical sigma L Kd (y : nativePoleNeutralParitySpace sigma L Kd)) := by
  have hz := isometricDetectorComplement_adjoint_eq_zero (nativeDetectorPredecessorEmbedding sigma s) y
  simp only [isometricDetectorCoupling, LinearMap.comp_apply, Submodule.subtype_apply,
    nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul, hz, smul_zero, sub_zero]

theorem nativeDetectorPredecessorEquiv_eq_compression (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s)
    (v : nativePoleNeutralParitySpace sigma L (s.cutoff - 1)) :
    nativeDetectorPredecessorEquiv sigma r v =
      (nativeDetectorPredecessorEmbedding sigma s).toLinearMap.adjoint
        (nativePoleNeutralParityShifted sigma L Kd (-s.eta)
          (nativeDetectorPredecessorEmbedding sigma s v)) := by
  let J := nativeDetectorPredecessorEmbedding sigma s
  have hcomp := nativePoleNeutralParity_predecessor_compression_eq sigma hL
    ((Nat.sub_le s.cutoff 1).trans s.cutoff_le_detector)
  have hcompv := congrArg (fun T => T v) hcomp
  change J.toLinearMap.adjoint (nativePoleNeutralParityCanonical sigma L Kd (J v)) =
    nativePoleNeutralParityCanonical sigma L (s.cutoff - 1) v at hcompv
  have hJ : J.toLinearMap.adjoint (J v) = v := by
    exact congrArg (fun T => T v) J.adjoint_comp_self'
  rw [nativeDetectorPredecessorEquiv_actual]
  simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul, hcompv, hJ]

/-- Exact DS for the original native parity detector at Kd. -/
theorem nativeDetectorSchur_completedSquare (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) (p : nativePoleNeutralParitySpace sigma L Kd) :
    let J := nativeDetectorPredecessorEmbedding sigma s
    let T := nativePoleNeutralParityShifted sigma L Kd (-s.eta)
    let P := nativeDetectorPredecessorEquiv sigma r
    let x := J.toLinearMap.adjoint p
    let y := isometricDetectorComplementCoordinate J p
    let z := x + isometricDetectorResponse J T P y
    inner ℂ (T p) p = inner ℂ (P z) z + inner ℂ (nativeDetectorSchurOperator sigma r y) y :=
  isometricDetectorSchur_completedSquare (nativeDetectorPredecessorEmbedding sigma s)
    (nativePoleNeutralParityShifted sigma L Kd (-s.eta))
    (nativePoleNeutralParityShifted_isSymmetric sigma L Kd (-s.eta))
    (nativeDetectorPredecessorEquiv sigma r) (nativeDetectorPredecessorEquiv_eq_compression sigma r) p

/-- The actual original unit detector retains negative Schur depth on the
whole detector complement. Its ground at another cutoff is not used here. -/
theorem nativeDetectorSchur_original_depth (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} (hD : 0 < D)
    {s : NativeDeepThresholdGroundData L Kd D hL} (r : NativeDeepThresholdInverseData s)
    (p : nativePoleNeutralParitySpace sigma L Kd) (hpUnit : ‖p‖ = 1)
    (hpDepth : (inner ℂ (nativePoleNeutralParityCanonical sigma L Kd p) p).re ≤ -D) :
    let y := isometricDetectorComplementCoordinate (nativeDetectorPredecessorEmbedding sigma s) p
    y ≠ 0 ∧ (inner ℂ (nativeDetectorSchurOperator sigma r y) y).re ≤ -(D - s.eta) ∧
      (inner ℂ (nativeDetectorSchurOperator sigma r y) y).re < -D / 2 := by
  have hpShift : (inner ℂ (nativePoleNeutralParityShifted sigma L Kd (-s.eta) p) p).re ≤ -(D - s.eta) := by
    have hs := @re_inner_ofReal_smul_self (nativePoleNeutralParitySpace sigma L Kd)
      inferInstance inferInstance (-s.eta) p
    simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, inner_sub_left, Complex.sub_re]
    rw [hpUnit] at hs
    norm_num at hs
    linarith
  have hpositive (v : nativePoleNeutralParitySpace sigma L (s.cutoff - 1)) :
      0 ≤ (inner ℂ (nativeDetectorPredecessorEquiv sigma r v) v).re := by
    have hg := nativeDeepThresholdGap_pos D Kd hD
      (s.cutoff_nonempty.trans s.cutoff_le_detector)
    rw [nativeDetectorPredecessorEquiv_actual]
    have hc : nativeDeepThresholdGap D Kd * ‖v‖ ^ 2 ≤
        (inner ℂ (nativePoleNeutralParityShifted sigma L (s.cutoff - 1) (-s.eta) v) v).re := by
      cases sigma
      · exact nativeDeepThreshold_even_detector_coercive s v
      · exact nativeDeepThreshold_odd_detector_coercive s v
    exact (mul_nonneg hg.le (sq_nonneg ‖v‖)).trans hc
  exact isometricDetectorSchur_negative_depth (nativeDetectorPredecessorEmbedding sigma s)
    (nativePoleNeutralParityShifted sigma L Kd (-s.eta))
    (nativePoleNeutralParityShifted_isSymmetric sigma L Kd (-s.eta))
    (nativeDetectorPredecessorEquiv sigma r) (nativeDetectorPredecessorEquiv_eq_compression sigma r)
    hpositive D s.eta hD s.eta_upper p hpShift

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleNeutralParity_predecessor_compression_eq
#print axioms Zeta23.CCM.nativeDetectorPredecessorEquiv_inverse_bound
#print axioms Zeta23.CCM.nativeDetectorComplement_finrank
#print axioms Zeta23.CCM.nativeDetectorCoupling_shift_eq_unshifted
#print axioms Zeta23.CCM.nativeDetectorPredecessorEquiv_eq_compression
#print axioms Zeta23.CCM.nativeDetectorSchur_completedSquare
#print axioms Zeta23.CCM.nativeDetectorSchur_original_depth
