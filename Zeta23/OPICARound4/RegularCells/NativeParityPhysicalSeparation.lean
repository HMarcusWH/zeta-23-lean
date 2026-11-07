import Zeta23.OPICARound4.RegularCells.NativeParityMatrixPencils

noncomputable section
namespace Zeta23.OPICARound4.NativeParityPencils
open CCM RegularCells NativeParitySeparation PrimeSourceLaurent Module.End

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  nativePoleNeutralParitySpace_innerProductSpace nativePoleNeutralParitySpace_normedAddCommGroup

/-- The physical frame need not be unitary. Its adjoint is a genuine equivalence. -/
def physicalAdjointEquiv (p : ReversalParity) {L : ℝ} (hL : 0 < L) (K : ℕ) :
    nativePoleNeutralParitySpace p L K ≃ₗ[ℂ] zeroCarrier p K :=
  LinearEquiv.ofBijective
    (LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K)
      (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap)
    (by
      refine ⟨physicalAdjoint_injective p hL K, ?_⟩
      let A : nativePoleNeutralParitySpace p L K →ₗ[ℂ] zeroCarrier p K :=
        LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K)
          (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap
      have hi : Function.Injective (A.comp (physicalEquiv p hL K).toLinearMap) :=
        (physicalAdjoint_injective p hL K).comp (physicalEquiv p hL K).injective
      have hs := LinearMap.surjective_of_injective hi
      intro v
      obtain ⟨u, hu⟩ := hs v
      exact ⟨physicalEquiv p hL K u, hu⟩)

private theorem physicalAdjointEquiv_toLinearMap (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    (physicalAdjointEquiv p hL K).toLinearMap =
      LinearMap.adjoint (𝕜 := ℂ) (E := zeroCarrier p K)
        (F := nativePoleNeutralParitySpace p L K) (physicalEquiv p hL K).toLinearMap := rfl

attribute [local irreducible] physicalEquiv physicalAdjointEquiv

private theorem nonzero_smul_injective_iff {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (T : E →ₗ[ℂ] F) (c : ℂ) (hc : c ≠ 0) :
    Function.Injective (c • T) ↔ Function.Injective T := by
  constructor
  · intro h x y hxy
    exact h (by simpa only [LinearMap.smul_apply] using congrArg (fun z => c • z) hxy)
  · intro h x y hxy
    apply h
    exact (smul_right_injective F hc) hxy

private theorem physicalFrame_injective_iff (L : ℝ) (K : ℕ)
    (A : poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralEvenSubspace L K)
    (B : poleNeutralOddSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K)
    (U : zeroCarrier .even K ≃ₗ[ℂ] poleNeutralEvenSubspace L K)
    (V : poleNeutralEvenSubspace L K ≃ₗ[ℂ] zeroCarrier .even K)
    (W : zeroCarrier .odd K ≃ₗ[ℂ] poleNeutralOddSubspace L K)
    (Y : poleNeutralOddSubspace L K ≃ₗ[ℂ] zeroCarrier .odd K) :
    Function.Injective (nativePencilSylvester
      (E := zeroCarrier .even K) (F := zeroCarrier .odd K)
      ((V.toLinearMap.comp A).comp U.toLinearMap) (V.toLinearMap.comp U.toLinearMap)
      ((Y.toLinearMap.comp B).comp W.toLinearMap) (Y.toLinearMap.comp W.toLinearMap)) ↔
    Function.Injective (nativeSylvester
      (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K) A B) := by
  let e : (zeroCarrier .even K →ₗ[ℂ] zeroCarrier .odd K) ≃ₗ[ℂ]
      (poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K) :=
    V.symm.arrowCongr W
  let f : (zeroCarrier .even K →ₗ[ℂ] zeroCarrier .odd K) ≃ₗ[ℂ]
      (poleNeutralEvenSubspace L K →ₗ[ℂ] poleNeutralOddSubspace L K) :=
    U.arrowCongr Y.symm
  let T := nativePencilSylvester
    (E := zeroCarrier .even K) (F := zeroCarrier .odd K)
    ((V.toLinearMap.comp A).comp U.toLinearMap) (V.toLinearMap.comp U.toLinearMap)
    ((Y.toLinearMap.comp B).comp W.toLinearMap) (Y.toLinearMap.comp W.toLinearMap)
  let S := nativeSylvester
    (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K) A B
  have hinter (X : zeroCarrier .even K →ₗ[ℂ] zeroCarrier .odd K) :
      f (T X) = S (e X) := by
    ext x
    simp [e, f, T, S, nativePencilSylvester, nativeSylvester]
  change Function.Injective T ↔ Function.Injective S
  constructor
  · intro hi X Z hxz
    obtain ⟨x,rfl⟩ := e.surjective X
    obtain ⟨z,rfl⟩ := e.surjective Z
    apply congrArg e
    apply hi
    apply f.injective
    simpa only [hinter] using hxz
  · intro hi X Z hxz
    apply e.injective
    apply hi
    simpa only [hinter] using congrArg f hxz

private theorem physicalSylvester_injective_iff_disjoint (L : ℝ) (K : ℕ) :
    Function.Injective (nativeSylvester
      (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K)
      (poleNeutralEvenCompressedCanonical L K) (poleNeutralOddCompressedCanonical L K)) ↔
    ∀ mu : ℂ, HasEigenvalue (poleNeutralEvenCompressedCanonical L K) mu →
      ¬ HasEigenvalue (poleNeutralOddCompressedCanonical L K) mu := by
  apply nativeSylvester_injective_iff_disjoint
  intro u v
  exact poleNeutralEvenCompressedCanonical_isSymmetric L K u v

theorem physicalFullPencil_injective_iff_disjoint {L : ℝ} (hL : 0 < L)
    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q) :
    Function.Injective (nativePencilSylvester
      (E := zeroCarrier .even K) (F := zeroCarrier .odd K)
      (frameEnergy .even K L (scaledPhysicalSource Q K L)) (frameGram .even K L)
      (frameEnergy .odd K L (scaledPhysicalSource Q K L)) (frameGram .odd K L)) ↔
    ∀ mu : ℂ, HasEigenvalue (nativePoleNeutralParityCanonical .even L K) mu →
      ¬ HasEigenvalue (nativePoleNeutralParityCanonical .odd L K) mu := by
  rw [frameEnergy_scaledPhysicalSource .even hL Q K hQ,
    frameEnergy_scaledPhysicalSource .odd hL Q K hQ,
    nativePencilSylvester_scale, nativePencilSylvester_common_scalar,
    nonzero_smul_injective_iff _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hL)),
    frameGram_physical .even hL, frameGram_physical .odd hL]
  rw [← physicalAdjointEquiv_toLinearMap .even hL K,
    ← physicalAdjointEquiv_toLinearMap .odd hL K]
  simp only [← LinearMap.comp_assoc]
  rw [physicalFrame_injective_iff L K]
  exact physicalSylvester_injective_iff_disjoint L K

theorem coordinateFrame_physical_det_iff_disjoint {L : ℝ} (hL : 0 < L)
    (Q K : ℕ) (hQ : ⌊Real.exp L⌋₊ = Q) :
    (formalRawFrameSylvester Q K (coordinateFrame .even K)
      (coordinateFrame .odd K) L (primePhaseUnits (boundedPrimeSet Q) L)).det ≠ 0 ↔
    ∀ mu : ℂ, HasEigenvalue (nativePoleNeutralParityCanonical .even L K) mu →
      ¬ HasEigenvalue (nativePoleNeutralParityCanonical .odd L K) mu := by
  rw [coordinateFrame_sylvester_det_iff, formalScaledSourceMatrix_actual_eq]
  exact physicalFullPencil_injective_iff_disjoint hL Q K hQ

end Zeta23.OPICARound4.NativeParityPencils
