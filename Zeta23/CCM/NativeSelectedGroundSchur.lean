import Zeta23.CCM.IsometricGroundSchur
import Zeta23.CCM.NativeDetectorSchur

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The selected ground uses the single successor shell at its selected
cutoff and the actual ground-relative shift lam. Its inverse budget is 6.
The detector operator remains a separate construction at Kd and -eta.
-/

def nativeSelectedGroundPredecessorEquiv (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) :
    nativePoleNeutralParitySpace sigma L (s.cutoff - 1) ≃ₗ[ℂ]
      nativePoleNeutralParitySpace sigma L (s.cutoff - 1) := by
  cases sigma
  · exact r.evenGround
  · exact r.oddGround

theorem nativeSelectedGroundPredecessorEquiv_actual (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) (v : nativePoleNeutralParitySpace sigma L (s.cutoff - 1)) :
    nativeSelectedGroundPredecessorEquiv sigma r v =
      nativePoleNeutralParityShifted sigma L (s.cutoff - 1) s.lam v := by
  cases sigma
  · exact r.evenGround_actual v
  · exact r.oddGround_actual v

theorem nativeSelectedGroundPredecessorEquiv_inverse_bound (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) :
    ‖(nativeSelectedGroundPredecessorEquiv sigma r).symm.toLinearMap.toContinuousLinearMap‖ ≤
      6 * ((Kd - 1 : ℕ) : ℝ) / D := by
  cases sigma
  · exact r.evenGround_inverse_bound
  · exact r.oddGround_inverse_bound

def nativeSelectedGroundPredecessorEmbedding (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) :
    nativePoleNeutralParitySpace sigma L (s.cutoff - 1) →ₗᵢ[ℂ]
      nativePoleNeutralParitySpace sigma L s.cutoff :=
  nativePoleNeutralParityCenteredZeroExtend sigma L (Nat.sub_le s.cutoff 1)

def nativeSelectedGroundShell (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) :
    Submodule ℂ (nativePoleNeutralParitySpace sigma L s.cutoff) :=
  isometricDetectorComplement (nativeSelectedGroundPredecessorEmbedding sigma s)

theorem nativeSelectedGroundShell_finrank_eq_one (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL) :
    Module.finrank ℂ (nativeSelectedGroundShell sigma s) = 1 := by
  let J := nativeSelectedGroundPredecessorEmbedding sigma s
  have hprev : 2 ≤ s.cutoff - 1 := by have hK := s.cutoff_nonempty; omega
  have hK : 2 ≤ s.cutoff := by have hK := s.cutoff_nonempty; omega
  have hs : Module.finrank ℂ (LinearMap.range J.toLinearMap) +
      Module.finrank ℂ (nativeSelectedGroundShell sigma s) =
      Module.finrank ℂ (nativePoleNeutralParitySpace sigma L s.cutoff) :=
    Submodule.finrank_add_finrank_orthogonal (LinearMap.range J.toLinearMap)
  have hr := LinearMap.finrank_range_of_inj (f := J.toLinearMap) J.injective
  rw [hr, finrank_nativePoleNeutralParitySpace sigma hL (s.cutoff - 1) hprev,
    finrank_nativePoleNeutralParitySpace sigma hL s.cutoff hK] at hs
  omega

def nativeSelectedGroundSchurOperator (sigma : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) :
    nativeSelectedGroundShell sigma s →ₗ[ℂ] nativeSelectedGroundShell sigma s :=
  isometricDetectorSchurOperator (nativeSelectedGroundPredecessorEmbedding sigma s)
    (nativePoleNeutralParityShifted sigma L s.cutoff s.lam)
    (nativeSelectedGroundPredecessorEquiv sigma r)

theorem nativeSelectedGroundPredecessorEquiv_eq_compression (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s)
    (v : nativePoleNeutralParitySpace sigma L (s.cutoff - 1)) :
    nativeSelectedGroundPredecessorEquiv sigma r v =
      (nativeSelectedGroundPredecessorEmbedding sigma s).toLinearMap.adjoint
        (nativePoleNeutralParityShifted sigma L s.cutoff s.lam
          (nativeSelectedGroundPredecessorEmbedding sigma s v)) := by
  let J := nativeSelectedGroundPredecessorEmbedding sigma s
  have hcomp := nativePoleNeutralParity_predecessor_compression_eq sigma hL (Nat.sub_le s.cutoff 1)
  have hcompv := congrArg (fun T => T v) hcomp
  change J.toLinearMap.adjoint (nativePoleNeutralParityCanonical sigma L s.cutoff (J v)) =
    nativePoleNeutralParityCanonical sigma L (s.cutoff - 1) v at hcompv
  have hJ : J.toLinearMap.adjoint (J v) = v :=
    congrArg (fun T => T v) J.adjoint_comp_self'
  dsimp only [J] at hcompv hJ
  rw [nativeSelectedGroundPredecessorEquiv_actual]
  simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul, hcompv, hJ]

/-- The actual ground retains its nonzero shell coordinate and exact
ground-relative predecessor response, even when the other parity is tied. -/
theorem nativeSelectedGroundSchur_kernel_package (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) (u : nativePoleNeutralParitySpace sigma L s.cutoff)
    (hu0 : u ≠ 0)
    (hu : nativePoleNeutralParityCanonical sigma L s.cutoff u = (s.lam : ℂ) • u) :
    let J := nativeSelectedGroundPredecessorEmbedding sigma s
    let T := nativePoleNeutralParityShifted sigma L s.cutoff s.lam
    let P := nativeSelectedGroundPredecessorEquiv sigma r
    let x := J.toLinearMap.adjoint u
    let y := isometricDetectorComplementCoordinate J u
    y ≠ 0 ∧ x = -isometricDetectorResponse J T P y ∧
      nativeSelectedGroundSchurOperator sigma r y = 0 := by
  have hshift : nativePoleNeutralParityShifted sigma L s.cutoff s.lam u = 0 := by
    simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hu, sub_self]
  exact isometricGroundSchur_kernel_package (nativeSelectedGroundPredecessorEmbedding sigma s)
    (nativePoleNeutralParityShifted sigma L s.cutoff s.lam)
    (nativeSelectedGroundPredecessorEquiv sigma r)
    (nativeSelectedGroundPredecessorEquiv_eq_compression sigma r) u hu0 hshift

/-- Basis-free selected-ground scalar equality d-lam=c*P_lam^-1 c,
homogeneously evaluated on its actual nonzero shell coordinate. -/
theorem nativeSelectedGround_shiftedSchur_eq (sigma : ReversalParity)
    {L D : ℝ} {Kd : ℕ} {hL : 0 < L} {s : NativeDeepThresholdGroundData L Kd D hL}
    (r : NativeDeepThresholdInverseData s) (u : nativePoleNeutralParitySpace sigma L s.cutoff)
    (hu0 : u ≠ 0)
    (hu : nativePoleNeutralParityCanonical sigma L s.cutoff u = (s.lam : ℂ) • u) :
    let J := nativeSelectedGroundPredecessorEmbedding sigma s
    let T := nativePoleNeutralParityShifted sigma L s.cutoff s.lam
    let P := nativeSelectedGroundPredecessorEquiv sigma r
    let y := isometricDetectorComplementCoordinate J u
    let response := isometricDetectorResponse J T P y
    inner ℂ (nativePoleNeutralParityCanonical sigma L s.cutoff
        (y : nativePoleNeutralParitySpace sigma L s.cutoff)) (y : nativePoleNeutralParitySpace sigma L s.cutoff) -
      (s.lam : ℂ) * inner ℂ (y : nativePoleNeutralParitySpace sigma L s.cutoff)
        (y : nativePoleNeutralParitySpace sigma L s.cutoff) =
      inner ℂ (P response) response := by
  obtain ⟨_, _, hschur⟩ := nativeSelectedGroundSchur_kernel_package sigma r u hu0 hu
  have hs := isometricGroundSchur_scalar_identity (nativeSelectedGroundPredecessorEmbedding sigma s)
    (nativePoleNeutralParityShifted sigma L s.cutoff s.lam)
    (nativePoleNeutralParityShifted_isSymmetric sigma L s.cutoff s.lam)
    (nativeSelectedGroundPredecessorEquiv sigma r)
    (nativeSelectedGroundPredecessorEquiv_eq_compression sigma r)
    (isometricDetectorComplementCoordinate (nativeSelectedGroundPredecessorEmbedding sigma s) u) hschur
  simpa only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, inner_sub_left, inner_smul_left, Complex.conj_ofReal] using hs

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeSelectedGroundPredecessorEquiv_inverse_bound
#print axioms Zeta23.CCM.nativeSelectedGroundShell_finrank_eq_one
#print axioms Zeta23.CCM.nativeSelectedGroundPredecessorEquiv_eq_compression
#print axioms Zeta23.CCM.nativeSelectedGroundSchur_kernel_package
#print axioms Zeta23.CCM.nativeSelectedGround_shiftedSchur_eq
