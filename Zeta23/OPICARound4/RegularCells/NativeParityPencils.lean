import Zeta23.OPICARound4.RegularCells.NativeZeroFrame
import Zeta23.OPICARound4.RegularCells.NativeZeroRegularity
import Zeta23.OPICARound4.RegularCells.PrimeSourceLaurent

noncomputable section
namespace Zeta23.OPICARound4.NativeParityPencils
open CCM RegularCells NativeZeroFrame NativeParitySeparation PrimeSourceLaurent
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  nativePoleNeutralParitySpace_innerProductSpace nativePoleNeutralParitySpace_normedAddCommGroup

abbrev zeroCarrier (p : ReversalParity) (K : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Fin K)) :=
  match p with
  | .even => nativeLimitingEvenCarrier K
  | .odd => nativeLimitingOddCarrier K

def rawFrame (p : ReversalParity) (K : ℕ) :
    zeroCarrier p K →ₗ[ℂ] EuclideanSpace ℂ (Fin (2*K+1)) := by
  cases p
  · exact (EuclideanSpace.equiv (Fin (2*K+1)) ℂ).symm.toLinearMap.comp
      ((fixedEvenSeed K).subtype.comp (evenZeroEquiv K).symm.toLinearMap)
  · exact (EuclideanSpace.equiv (Fin (2*K+1)) ℂ).symm.toLinearMap.comp
      ((fixedOddSeed K).subtype.comp (oddZeroEquiv K).symm.toLinearMap)

def physicalEquiv (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    zeroCarrier p K ≃ₗ[ℂ] nativePoleNeutralParitySpace p L K := by
  cases p
  · exact (evenZeroEquiv K).symm.trans (fixedEvenSeedPhysicalEquiv hL K)
  · exact (oddZeroEquiv K).symm.trans (fixedOddSeedPhysicalEquiv hL K)

def physicalDiagonal (K : ℕ) (z : ℂ) :
    Matrix (Fin (2*K+1)) (Fin (2*K+1)) ℂ :=
  Matrix.diagonal (fun i => (z / (4 * (Real.pi : ℂ)))^2 + (centeredIndex K i : ℂ)^2)

theorem physicalDiagonal_ofReal (K : ℕ) (L : ℝ) :
    physicalDiagonal K (L : ℂ) =
      Matrix.diagonal (fun i => (fixedSeedDiagonalEntry L K i : ℂ)) := by
  ext i j
  simp [physicalDiagonal, fixedSeedDiagonalEntry, fixedSeedParameter]

theorem physicalDiagonal_real_isSymmetric (K : ℕ) (L : ℝ) :
    (physicalDiagonal K (L : ℂ)).toEuclideanLin.IsSymmetric := by
  rw [physicalDiagonal_ofReal]
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff]

theorem physicalDiagonal_apply (K : ℕ) (L : ℝ)
    (u : EuclideanSpace ℂ (Fin (2*K+1))) :
    (physicalDiagonal K (L : ℂ)).toEuclideanLin u =
      WithLp.toLp 2 (fixedSeedDiagonal L K u.ofLp) := by
  ext i
  rw [physicalDiagonal_ofReal]
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  rfl

theorem diagonal_rawFrame_physical (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : zeroCarrier p K) :
    (physicalDiagonal K (L : ℂ)).toEuclideanLin (rawFrame p K u) =
      nativeSeedAmbientIsometry p L K (physicalEquiv p hL K u) := by
  rw [physicalDiagonal_ofReal]
  cases p <;> ext i <;> simp only [Matrix.toLpLin_apply, Matrix.mulVec_diagonal] <;> rfl

def frameGram (p : ReversalParity) (K : ℕ) (z : ℂ) :
    Module.End ℂ (zeroCarrier p K) :=
  (LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K) (F := EuclideanSpace ℂ (Fin (2*K+1))) (rawFrame p K)).comp ((physicalDiagonal K z).toEuclideanLin.comp
    ((physicalDiagonal K z).toEuclideanLin.comp (rawFrame p K)))

def frameEnergy (p : ReversalParity) (K : ℕ) (z : ℂ)
    (S : Matrix (Fin (2*K+1)) (Fin (2*K+1)) ℂ) :
    Module.End ℂ (zeroCarrier p K) :=
  (LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K) (F := EuclideanSpace ℂ (Fin (2*K+1))) (rawFrame p K)).comp ((physicalDiagonal K z).toEuclideanLin.comp
    (S.toEuclideanLin.comp ((physicalDiagonal K z).toEuclideanLin.comp (rawFrame p K))))

theorem frameGram_physical (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    frameGram p K L = (LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K) (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap).comp
      (physicalEquiv p hL K).toLinearMap := by
  ext x : 1
  apply ext_inner_right ℂ
  intro y
  simp only [frameGram, LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [physicalDiagonal_real_isSymmetric K L,
    diagonal_rawFrame_physical p hL K x, diagonal_rawFrame_physical p hL K y]
  exact (nativeSeedAmbientIsometry p L K).inner_map_map _ _

theorem frameEnergy_canonical_physical (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) :
    frameEnergy p K L (canonicalSourceMatrix L K) =
      (LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K) (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap).comp
        ((nativePoleNeutralParityCanonical p L K).comp (physicalEquiv p hL K).toLinearMap) := by
  ext x : 1
  apply ext_inner_right ℂ
  intro y
  simp only [frameEnergy, LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [physicalDiagonal_real_isSymmetric K L,
    diagonal_rawFrame_physical p hL K x, diagonal_rawFrame_physical p hL K y]
  exact (nativeSeedAmbientIsometry_inner_canonical p L K _ _).symm

theorem frameGram_zero (p : ReversalParity) (K : ℕ) :
    frameGram p K 0 = (2 : ℂ) • LinearMap.id := by
  ext x : 1
  apply ext_inner_right ℂ
  intro y
  simp only [frameGram, LinearMap.comp_apply, LinearMap.adjoint_inner_left]
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl,
    physicalDiagonal_real_isSymmetric K 0, physicalDiagonal_apply, physicalDiagonal_apply]
  cases p
  · change inner ℂ
      (WithLp.toLp 2 (fixedSeedDiagonal 0 K ((evenZeroEquiv K).symm x)) : EuclideanSpace ℂ _)
      (WithLp.toLp 2 (fixedSeedDiagonal 0 K ((evenZeroEquiv K).symm y))) = _
    rw [zero_even_gram]
    simp only [LinearEquiv.apply_symm_apply, LinearMap.smul_apply, LinearMap.id_apply]
    change 2 * inner ℂ x.val y.val = inner ℂ ((2 : ℂ) • x.val) y.val
    rw [_root_.inner_smul_left]
    have hc : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_natCast 2
    rw [hc]
  · change inner ℂ
      (WithLp.toLp 2 (fixedSeedDiagonal 0 K ((oddZeroEquiv K).symm x)) : EuclideanSpace ℂ _)
      (WithLp.toLp 2 (fixedSeedDiagonal 0 K ((oddZeroEquiv K).symm y))) = _
    rw [zero_odd_gram]
    simp only [LinearEquiv.apply_symm_apply, LinearMap.smul_apply, LinearMap.id_apply]
    change 2 * inner ℂ x.val y.val = inner ℂ ((2 : ℂ) • x.val) y.val
    rw [_root_.inner_smul_left]
    have hc : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_natCast 2
    rw [hc]

def scaledPhysicalSource (Q K : ℕ) (z : ℂ) :
    Matrix (Fin (2*K+1)) (Fin (2*K+1)) ℂ :=
  (-z) • complexCanonicalArchWithoutWMatrix z K -
    scaledFrozenPrimeMatrix Q z (fun q => integerPhase q z) K

def physicalCommonShift (Q : ℕ) (L : ℝ) : ℂ :=
  ((2 * wCorrection L : ℝ) : ℂ) + primeCommonScalar Q L

theorem scaledPhysicalSource_eq (Q K : ℕ) {L : ℝ} (hL : 0 < L)
    (hQ : ⌊Real.exp L⌋₊ = Q) :
    scaledPhysicalSource Q K L = (L : ℂ) •
      (canonicalSourceMatrix L K - canonicalPoleMatrix L K +
        physicalCommonShift Q L • 1) := by
  have hz : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hL)
  rw [scaledPhysicalSource, scaledFrozenPrimeMatrix_eq Q hz,
    formalFrozenPrimeMatrix_actual, complexCanonicalArchWithoutWMatrix_ofReal hL,
    complexFrozenCanonicalPrimeMatrix_ofReal,
    frozenCanonicalPrimeMatrix_eq_canonicalPrimeMatrix L K hQ,
    canonicalSourceMatrix_eq_pole_sub_arch_sub_prime,
    canonicalArchMatrix_eq_withoutW_add_scalar]
  unfold physicalCommonShift
  module

theorem diagonal_rawFrame_profiles (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : zeroCarrier p K) :
    poleEvenProfile L K ⬝ᵥ ((physicalDiagonal K L).toEuclideanLin (rawFrame p K u)).ofLp = 0 ∧
    poleOddProfile L K ⬝ᵥ ((physicalDiagonal K L).toEuclideanLin (rawFrame p K u)).ofLp = 0 := by
  apply (canonicalPoleExponentialMoments_iff_profiles hL K _).mp
  rw [physicalDiagonal_apply]
  cases p
  · exact fixedEvenSeedPhysicalEquiv_exponentialMoments hL K ((evenZeroEquiv K).symm u)
  · exact fixedOddSeedPhysicalEquiv_exponentialMoments hL K ((oddZeroEquiv K).symm u)

theorem frameEnergy_pole_zero (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    frameEnergy p K L (canonicalPoleMatrix L K) = 0 := by
  ext x : 1
  have hp := canonicalPoleMatrix_mulVec_eq_zero_of_profiles hL K _
    (diagonal_rawFrame_profiles p hL K x).1 (diagonal_rawFrame_profiles p hL K x).2
  have hv : (canonicalPoleMatrix L K).toEuclideanLin
      ((physicalDiagonal K L).toEuclideanLin (rawFrame p K x)) = 0 := by
    exact congrArg (WithLp.toLp 2) hp
  simp only [frameEnergy, LinearMap.comp_apply, hv, map_zero, LinearMap.zero_apply]

theorem frameEnergy_add (p : ReversalParity) (K : ℕ) (z : ℂ)
    (A B : Matrix (Fin (2*K+1)) (Fin (2*K+1)) ℂ) :
    frameEnergy p K z (A+B) = frameEnergy p K z A + frameEnergy p K z B := by
  ext x : 1
  simp [frameEnergy, map_add]

theorem frameEnergy_smul (p : ReversalParity) (K : ℕ) (z c : ℂ)
    (A : Matrix (Fin (2*K+1)) (Fin (2*K+1)) ℂ) :
    frameEnergy p K z (c • A) = c • frameEnergy p K z A := by
  ext x : 1
  simp [frameEnergy, map_smul]

theorem frameEnergy_identity (p : ReversalParity) (K : ℕ) (z : ℂ) :
    frameEnergy p K z 1 = frameGram p K z := by
  simp [frameEnergy, frameGram]

theorem frameEnergy_sub (p : ReversalParity) (K : ℕ) (z : ℂ)
    (A B : Matrix (Fin (2*K+1)) (Fin (2*K+1)) ℂ) :
    frameEnergy p K z (A-B) = frameEnergy p K z A - frameEnergy p K z B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ B, frameEnergy_add, frameEnergy_smul]
  rw [neg_one_smul ℂ (frameEnergy p K z B), sub_eq_add_neg]

theorem frameEnergy_scaledPhysicalSource (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q) :
    frameEnergy p K L (scaledPhysicalSource Q K L) = (L : ℂ) •
      ((LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K) (F := nativePoleNeutralParitySpace p L K)
          (physicalEquiv p hL K).toLinearMap).comp
          ((nativePoleNeutralParityCanonical p L K).comp (physicalEquiv p hL K).toLinearMap) +
        physicalCommonShift Q L • frameGram p K L) := by
  rw [scaledPhysicalSource_eq Q K hL hQ, frameEnergy_smul, frameEnergy_add,
    frameEnergy_sub, frameEnergy_pole_zero p hL, sub_zero,
    frameEnergy_canonical_physical p hL, frameEnergy_smul, frameEnergy_identity]

theorem physicalAdjoint_injective (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    Function.Injective (LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K)
      (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap) := by
  intro x y h
  apply ext_inner_right ℂ
  intro v
  obtain ⟨w, rfl⟩ := (physicalEquiv p hL K).surjective v
  have hx := LinearMap.adjoint_inner_left (𝕜 := ℂ) (E := zeroCarrier p K)
    (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap w x
  have hy := LinearMap.adjoint_inner_left (𝕜 := ℂ) (E := zeroCarrier p K)
    (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap w y
  exact hx.symm.trans ((congrArg (fun z => inner ℂ z w) h).trans hy)

theorem physical_pencil_eigen_iff (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q) (mu : ℂ) (u : zeroCarrier p K) :
    frameEnergy p K L (scaledPhysicalSource Q K L) u =
        ((L : ℂ) * (mu + physicalCommonShift Q L)) • frameGram p K L u ↔
      nativePoleNeutralParityCanonical p L K (physicalEquiv p hL K u) =
        mu • physicalEquiv p hL K u := by
  rw [frameEnergy_scaledPhysicalSource p hL Q K hQ, frameGram_physical p hL]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, mul_smul]
  have hinj : Function.Injective (fun v : zeroCarrier p K => (L : ℂ) • v) :=
    smul_right_injective (zeroCarrier p K) (Complex.ofReal_ne_zero.mpr (ne_of_gt hL))
  rw [hinj.eq_iff]
  let V : nativePoleNeutralParitySpace p L K →ₗ[ℂ] zeroCarrier p K :=
    LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K)
      (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap
  change V (nativePoleNeutralParityCanonical p L K (physicalEquiv p hL K u)) +
      physicalCommonShift Q L • V (physicalEquiv p hL K u) =
        (mu + physicalCommonShift Q L) • V (physicalEquiv p hL K u) ↔ _
  rw [← V.map_smul (physicalCommonShift Q L) (physicalEquiv p hL K u),
    ← V.map_add,
    ← V.map_smul (mu + physicalCommonShift Q L) (physicalEquiv p hL K u),
    (physicalAdjoint_injective p hL K).eq_iff]
  simp only [add_smul, add_left_inj]

theorem physical_pencil_nonzero_eigen_iff (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q) (mu : ℂ) :
    (∃ u : zeroCarrier p K, u ≠ 0 ∧
      frameEnergy p K L (scaledPhysicalSource Q K L) u =
        ((L : ℂ) * (mu + physicalCommonShift Q L)) • frameGram p K L u) ↔
    ∃ v : nativePoleNeutralParitySpace p L K, v ≠ 0 ∧
      nativePoleNeutralParityCanonical p L K v = mu • v := by
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨physicalEquiv p hL K u, (by simpa using hu),
      (physical_pencil_eigen_iff p hL Q K hQ mu u).mp he⟩
  · rintro ⟨v, hv, he⟩
    refine ⟨(physicalEquiv p hL K).symm v, (by simpa using hv), ?_⟩
    apply (physical_pencil_eigen_iff p hL Q K hQ mu _).mpr
    simpa using he


end Zeta23.OPICARound4.NativeParityPencils
