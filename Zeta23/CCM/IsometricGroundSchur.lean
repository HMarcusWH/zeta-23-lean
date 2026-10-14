import Zeta23.CCM.IsometricDetectorSchur

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

theorem isometricDetectorComplementCoordinate_mem (J : E →ₗᵢ[ℂ] F)
    (y : isometricDetectorComplement J) : isometricDetectorComplementCoordinate J (y : F) = y := by
  apply Subtype.ext
  rw [coe_isometricDetectorComplementCoordinate,
    isometricDetectorComplement_adjoint_eq_zero, map_zero, sub_zero]

/-- A nonzero ground in the kernel of the shifted full operator has a
nonzero actual shell coordinate. Its whole predecessor coordinate is
resolved by that shift's predecessor inverse. -/
theorem isometricGroundSchur_kernel_package (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (Ti : E ≃ₗ[ℂ] E) (hTi : ∀ v, Ti v = J.toLinearMap.adjoint (T (J v)))
    (u : F) (hu0 : u ≠ 0) (hu : T u = 0) :
    let x := J.toLinearMap.adjoint u
    let y := isometricDetectorComplementCoordinate J u
    y ≠ 0 ∧ x = -isometricDetectorResponse J T Ti y ∧
      isometricDetectorSchurOperator J T Ti y = 0 := by
  let x := J.toLinearMap.adjoint u
  let y := isometricDetectorComplementCoordinate J u
  let b := isometricDetectorCoupling J T y
  let r := isometricDetectorResponse J T Ti y
  have hrec : J x + (y : F) = u := isometricDetector_coordinate_decomposition J u
  have hblock : Ti x + b = 0 := by
    have hj := congrArg J.toLinearMap.adjoint hu
    rw [← hrec, map_add, map_add, ← hTi] at hj
    simpa only [map_zero] using hj
  have hx : x = -r := by
    have hxb : Ti x = -b := eq_neg_of_add_eq_zero_left hblock
    have hs := congrArg Ti.symm hxb
    rw [Ti.symm_apply_apply, map_neg] at hs
    exact hs
  have huDecomp : u = (y : F) - J r := by
    rw [← hrec, hx, map_neg]
    abel
  have hschur : isometricDetectorSchurOperator J T Ti y = 0 := by
    change isometricDetectorComplementCoordinate J (T ((y : F) - J r)) = 0
    rw [← huDecomp, hu, map_zero]
  refine ⟨?_, hx, hschur⟩
  intro hy
  apply hu0
  rw [huDecomp]
  change (y : F) - J (isometricDetectorResponse J T Ti y) = 0
  simp only [hy, map_zero, Submodule.coe_zero, sub_zero]

/-- The actual ground shell's scalar Schur equality uses its actual
response at the ground shift, independently of any detector threshold. -/
theorem isometricGroundSchur_scalar_identity (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (Ti : E ≃ₗ[ℂ] E)
    (hTi : ∀ v, Ti v = J.toLinearMap.adjoint (T (J v)))
    (y : isometricDetectorComplement J) (hy : isometricDetectorSchurOperator J T Ti y = 0) :
    inner ℂ (T (y : F)) (y : F) =
      inner ℂ (Ti (isometricDetectorResponse J T Ti y)) (isometricDetectorResponse J T Ti y) := by
  have hs := isometricDetectorSchur_completedSquare J T hT Ti hTi (y : F)
  simpa only [isometricDetectorComplement_adjoint_eq_zero,
    isometricDetectorComplementCoordinate_mem, zero_add, hy, inner_zero_left, add_zero] using hs

end Zeta23.CCM

#print axioms Zeta23.CCM.isometricGroundSchur_kernel_package
#print axioms Zeta23.CCM.isometricGroundSchur_scalar_identity
