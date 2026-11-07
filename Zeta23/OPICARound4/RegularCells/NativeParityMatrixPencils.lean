import Zeta23.OPICARound4.RegularCells.NativeParityPencils
import Zeta23.OPICARound4.RegularCells.MatrixSylvesterCoordinates

noncomputable section
namespace Zeta23.OPICARound4.NativeParityPencils
open CCM RegularCells NativeZeroFrame NativeParitySeparation PrimeSourceLaurent
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  nativePoleNeutralParitySpace_innerProductSpace nativePoleNeutralParitySpace_normedAddCommGroup

abbrev coordinateIndex (p : ReversalParity) (K : ℕ) :=
  Fin (Module.finrank ℂ (zeroCarrier p K))

def coordinateIsometry (p : ReversalParity) (K : ℕ) :
    EuclideanSpace ℂ (coordinateIndex p K) ≃ₗᵢ[ℂ] zeroCarrier p K :=
  (stdOrthonormalBasis ℂ (zeroCarrier p K)).repr.symm

attribute [local irreducible] coordinateIsometry

def coordinateFrame (p : ReversalParity) (K : ℕ) :
    Matrix (Fin (2*K+1)) (coordinateIndex p K) ℂ :=
  Matrix.toEuclideanLin.symm
    ((rawFrame p K).comp (coordinateIsometry p K).toLinearMap)

theorem coordinateFrame_toEuclideanLin (p : ReversalParity) (K : ℕ) :
    (coordinateFrame p K).toEuclideanLin =
      (rawFrame p K).comp (coordinateIsometry p K).toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

theorem rawPhysicalDiagonal_eq (K : ℕ) (z : ℂ) :
    rawPhysicalDiagonal K z = physicalDiagonal K z := rfl

theorem formalScaledSourceMatrix_actual_eq (Q K : ℕ) (z : ℂ) :
    formalScaledSourceMatrix Q z (primePhaseUnits (boundedPrimeSet Q) z) K =
      scaledPhysicalSource Q K z := by
  rw [formalScaledSourceMatrix_actual]
  rfl

theorem coordinateFrame_gram (p : ReversalParity) (K : ℕ) (z : ℂ) :
    (formalRawFrameGram K (coordinateFrame p K) z).toEuclideanLin =
      (LinearMap.adjoint (𝕜 := ℂ) (E := EuclideanSpace ℂ (coordinateIndex p K)) (F := zeroCarrier p K) (coordinateIsometry p K).toLinearMap).comp
        ((frameGram p K z).comp (coordinateIsometry p K).toLinearMap) := by
  have hadj := LinearMap.adjoint_comp (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (coordinateIndex p K)) (F := zeroCarrier p K)
    (G := EuclideanSpace ℂ (Fin (2*K+1)))
    (rawFrame p K) (coordinateIsometry p K).toLinearMap
  rw [formalRawFrameGram, rawPhysicalDiagonal_eq]
  simp only [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    coordinateFrame_toEuclideanLin, hadj, frameGram,
    LinearMap.comp_assoc]

theorem coordinateFrame_energy (p : ReversalParity) (Q K : ℕ) (z : ℂ)
    (X : boundedPrimeSet Q → ℂˣ) :
    (formalRawFrameEnergy Q K (coordinateFrame p K) z X).toEuclideanLin =
      (LinearMap.adjoint (𝕜 := ℂ) (E := EuclideanSpace ℂ (coordinateIndex p K)) (F := zeroCarrier p K) (coordinateIsometry p K).toLinearMap).comp
        ((frameEnergy p K z (formalScaledSourceMatrix Q z X K)).comp
          (coordinateIsometry p K).toLinearMap) := by
  have hadj := LinearMap.adjoint_comp (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (coordinateIndex p K)) (F := zeroCarrier p K)
    (G := EuclideanSpace ℂ (Fin (2*K+1)))
    (rawFrame p K) (coordinateIsometry p K).toLinearMap
  rw [formalRawFrameEnergy, rawPhysicalDiagonal_eq]
  simp only [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    coordinateFrame_toEuclideanLin, hadj, frameEnergy,
    LinearMap.comp_assoc]

def coordinatePhysicalEquiv (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    EuclideanSpace ℂ (coordinateIndex p K) ≃ₗ[ℂ] nativePoleNeutralParitySpace p L K :=
  (coordinateIsometry p K).toLinearEquiv.trans (physicalEquiv p hL K)

theorem coordinateFrame_gram_physical (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    (formalRawFrameGram K (coordinateFrame p K) L).toEuclideanLin =
      (LinearMap.adjoint (𝕜 := ℂ) (E := EuclideanSpace ℂ (coordinateIndex p K)) (F := nativePoleNeutralParitySpace p L K) (coordinatePhysicalEquiv p hL K).toLinearMap).comp
        (coordinatePhysicalEquiv p hL K).toLinearMap := by
  have hadj := LinearMap.adjoint_comp (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (coordinateIndex p K)) (F := zeroCarrier p K)
    (G := nativePoleNeutralParitySpace p L K)
    (physicalEquiv p hL K).toLinearMap (coordinateIsometry p K).toLinearMap
  rw [coordinateFrame_gram, frameGram_physical p hL]
  simp only [coordinatePhysicalEquiv, LinearEquiv.coe_trans,
    hadj, LinearMap.comp_assoc]

theorem coordinateFrame_energy_physical (p : ReversalParity) {L : ℝ} (hL : 0 < L)
    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q) :
    (formalRawFrameEnergy Q K (coordinateFrame p K) L
      (primePhaseUnits (boundedPrimeSet Q) L)).toEuclideanLin =
      (L : ℂ) •
        (((LinearMap.adjoint (𝕜 := ℂ)
          (E := EuclideanSpace ℂ (coordinateIndex p K))
          (F := nativePoleNeutralParitySpace p L K)
          (coordinatePhysicalEquiv p hL K).toLinearMap).comp
            ((nativePoleNeutralParityCanonical p L K).comp
              (coordinatePhysicalEquiv p hL K).toLinearMap)) +
          physicalCommonShift Q L •
            (formalRawFrameGram K (coordinateFrame p K) L).toEuclideanLin) := by
  have hadj := LinearMap.adjoint_comp (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (coordinateIndex p K)) (F := zeroCarrier p K)
    (G := nativePoleNeutralParitySpace p L K)
    (physicalEquiv p hL K).toLinearMap (coordinateIsometry p K).toLinearMap
  rw [coordinateFrame_energy, formalScaledSourceMatrix_actual_eq,
    frameEnergy_scaledPhysicalSource p hL Q K hQ, coordinateFrame_gram]
  simp only [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_add,
    LinearMap.add_comp, coordinatePhysicalEquiv, LinearEquiv.coe_trans,
    hadj, LinearMap.comp_assoc]

private theorem coordinateIsometry_pencil_injective_iff (K : ℕ)
    (U : EuclideanSpace ℂ (coordinateIndex .even K) ≃ₗᵢ[ℂ] zeroCarrier .even K)
    (V : EuclideanSpace ℂ (coordinateIndex .odd K) ≃ₗᵢ[ℂ] zeroCarrier .odd K)
    (He Ge : Module.End ℂ (zeroCarrier .even K))
    (Ho Go : Module.End ℂ (zeroCarrier .odd K)) :
    Function.Injective (nativePencilSylvester
      (E := EuclideanSpace ℂ (coordinateIndex .even K))
      (F := EuclideanSpace ℂ (coordinateIndex .odd K))
      ((LinearMap.adjoint (𝕜 := ℂ)
        (E := EuclideanSpace ℂ (coordinateIndex .even K)) (F := zeroCarrier .even K)
        U.toLinearMap).comp
          (He.comp U.toLinearMap))
      ((LinearMap.adjoint (𝕜 := ℂ)
        (E := EuclideanSpace ℂ (coordinateIndex .even K)) (F := zeroCarrier .even K)
        U.toLinearMap).comp
          (Ge.comp U.toLinearMap))
      ((LinearMap.adjoint (𝕜 := ℂ)
        (E := EuclideanSpace ℂ (coordinateIndex .odd K)) (F := zeroCarrier .odd K)
        V.toLinearMap).comp
          (Ho.comp V.toLinearMap))
      ((LinearMap.adjoint (𝕜 := ℂ)
        (E := EuclideanSpace ℂ (coordinateIndex .odd K)) (F := zeroCarrier .odd K)
        V.toLinearMap).comp
          (Go.comp V.toLinearMap))) ↔
      Function.Injective (nativePencilSylvester
        (E := zeroCarrier .even K) (F := zeroCarrier .odd K) He Ge Ho Go) := by
  have hu := LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (𝕜 := ℂ)
    (H := EuclideanSpace ℂ (coordinateIndex .even K)) (K := zeroCarrier .even K) U
  have hv := LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (𝕜 := ℂ)
    (H := EuclideanSpace ℂ (coordinateIndex .odd K)) (K := zeroCarrier .odd K) V
  rw [hu, hv]
  let e : (EuclideanSpace ℂ (coordinateIndex .even K) →ₗ[ℂ]
      EuclideanSpace ℂ (coordinateIndex .odd K)) ≃ₗ[ℂ]
      (zeroCarrier .even K →ₗ[ℂ] zeroCarrier .odd K) :=
    U.toLinearEquiv.arrowCongr V.toLinearEquiv
  let T := nativePencilSylvester
    (E := EuclideanSpace ℂ (coordinateIndex .even K))
    (F := EuclideanSpace ℂ (coordinateIndex .odd K))
    (U.symm.toLinearMap.comp (He.comp U.toLinearMap))
    (U.symm.toLinearMap.comp (Ge.comp U.toLinearMap))
    (V.symm.toLinearMap.comp (Ho.comp V.toLinearMap))
    (V.symm.toLinearMap.comp (Go.comp V.toLinearMap))
  let S := nativePencilSylvester
    (E := zeroCarrier .even K) (F := zeroCarrier .odd K) He Ge Ho Go
  have hinter (W : EuclideanSpace ℂ (coordinateIndex .even K) →ₗ[ℂ]
      EuclideanSpace ℂ (coordinateIndex .odd K)) : e (T W) = S (e W) := by
    ext x
    simp [e, T, S, nativePencilSylvester]
  change Function.Injective T ↔ Function.Injective S
  constructor
  · intro hi A B hab
    obtain ⟨a,rfl⟩ := e.surjective A
    obtain ⟨b,rfl⟩ := e.surjective B
    apply congrArg e
    apply hi
    apply e.injective
    simpa only [hinter] using hab
  · intro hi A B hab
    apply e.injective
    apply hi
    simpa only [hinter] using congrArg e hab

/-- The coordinate determinant is exactly the full native Gram pencil on the limiting
carriers. This is a basis change, not an orthonormality claim about the physical frame. -/
theorem coordinateFrame_sylvester_det_iff (Q K : ℕ) (z : ℂ)
    (X : boundedPrimeSet Q → ℂˣ) :
    (formalRawFrameSylvester Q K (coordinateFrame .even K)
      (coordinateFrame .odd K) z X).det ≠ 0 ↔
    Function.Injective (nativePencilSylvester
      (E := zeroCarrier .even K) (F := zeroCarrier .odd K)
      (frameEnergy .even K z (formalScaledSourceMatrix Q z X K)) (frameGram .even K z)
      (frameEnergy .odd K z (formalScaledSourceMatrix Q z X K)) (frameGram .odd K z)) := by
  rw [formalRawFrameSylvester_det_iff_coordinate_injective,
    coordinateFrame_energy, coordinateFrame_gram, coordinateFrame_energy, coordinateFrame_gram]
  exact coordinateIsometry_pencil_injective_iff K
    (coordinateIsometry .even K) (coordinateIsometry .odd K) _ _ _ _

end Zeta23.OPICARound4.NativeParityPencils
