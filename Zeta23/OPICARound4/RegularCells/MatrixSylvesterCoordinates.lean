import Zeta23.OPICARound4.RegularCells.NativePrimeExpansion
import Zeta23.OPICARound4.RegularCells.SylvesterSeparation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
namespace Zeta23.OPICARound4.NativeParitySeparation
open PrimeSourceLaurent Matrix

section Matrix
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem formalRawFrameSylvester_det_iff_matrix_injective (Q K : ℕ)
    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ)
    (z : ℂ) (X : boundedPrimeSet Q → ℂˣ) :
    (formalRawFrameSylvester Q K Ce Co z X).det ≠ 0 ↔
      Function.Injective (fun V : Matrix κ ι ℂ =>
        formalRawFrameEnergy Q K Co z X * V * formalRawFrameGram K Ce z -
          formalRawFrameGram K Co z * V * formalRawFrameEnergy Q K Ce z X) := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro h V W hw
    have hv : (fun ij : κ × ι => V ij.1 ij.2) = (fun ij => W ij.1 ij.2) := by
      apply h
      funext ij
      rcases ij with ⟨i,j⟩
      rw [formalRawFrameSylvester_mulVec, formalRawFrameSylvester_mulVec]
      exact congrArg (fun M : Matrix κ ι ℂ => M i j) hw
    ext i j
    exact congrFun hv (i,j)
  · intro h v w hv
    have hm : (fun i j => v (i,j)) = (fun i j => w (i,j)) := by
      apply h
      ext i j
      change (formalRawFrameEnergy Q K Co z X * (show Matrix κ ι ℂ from fun i j => v (i,j)) *
          formalRawFrameGram K Ce z - formalRawFrameGram K Co z *
          (show Matrix κ ι ℂ from fun i j => v (i,j)) * formalRawFrameEnergy Q K Ce z X) i j =
        (formalRawFrameEnergy Q K Co z X * (show Matrix κ ι ℂ from fun i j => w (i,j)) *
          formalRawFrameGram K Ce z - formalRawFrameGram K Co z *
          (show Matrix κ ι ℂ from fun i j => w (i,j)) * formalRawFrameEnergy Q K Ce z X) i j
      calc
        _ = (formalRawFrameSylvester Q K Ce Co z X *ᵥ v) (i,j) := by
          simpa using (formalRawFrameSylvester_mulVec Q K Ce Co z X
            (fun i j => v (i,j)) i j).symm
        _ = (formalRawFrameSylvester Q K Ce Co z X *ᵥ w) (i,j) := congrFun hv (i,j)
        _ = _ := by
          simpa using formalRawFrameSylvester_mulVec Q K Ce Co z X
            (fun i j => w (i,j)) i j
    funext ij
    exact congrFun (congrFun hm ij.1) ij.2

theorem matrix_pencil_toEuclideanLin (He Ge : Matrix ι ι ℂ)
    (Ho Go : Matrix κ κ ℂ) (V : Matrix κ ι ℂ) :
    (Ho * V * Ge - Go * V * He).toEuclideanLin =
      nativePencilSylvester He.toEuclideanLin Ge.toEuclideanLin
        Ho.toEuclideanLin Go.toEuclideanLin V.toEuclideanLin := by
  simp only [map_sub, Matrix.toLpLin_mul_same]
  rfl

theorem matrix_pencil_injective_iff (He Ge : Matrix ι ι ℂ)
    (Ho Go : Matrix κ κ ℂ) :
    Function.Injective (fun V : Matrix κ ι ℂ => Ho * V * Ge - Go * V * He) ↔
      Function.Injective (nativePencilSylvester He.toEuclideanLin Ge.toEuclideanLin
        Ho.toEuclideanLin Go.toEuclideanLin) := by
  constructor
  · intro h V W hv
    obtain ⟨v,rfl⟩ := Matrix.toEuclideanLin.surjective V
    obtain ⟨w,rfl⟩ := Matrix.toEuclideanLin.surjective W
    apply congrArg Matrix.toEuclideanLin
    apply h
    apply Matrix.toEuclideanLin.injective
    simpa only [matrix_pencil_toEuclideanLin] using hv
  · intro h V W hv
    apply Matrix.toEuclideanLin.injective
    apply h
    simpa only [matrix_pencil_toEuclideanLin] using congrArg Matrix.toEuclideanLin hv

theorem formalRawFrameSylvester_det_iff_coordinate_injective (Q K : ℕ)
    (Ce : Matrix (Fin (2*K+1)) ι ℂ) (Co : Matrix (Fin (2*K+1)) κ ℂ)
    (z : ℂ) (X : boundedPrimeSet Q → ℂˣ) :
    (formalRawFrameSylvester Q K Ce Co z X).det ≠ 0 ↔
      Function.Injective (nativePencilSylvester
        (formalRawFrameEnergy Q K Ce z X).toEuclideanLin
        (formalRawFrameGram K Ce z).toEuclideanLin
        (formalRawFrameEnergy Q K Co z X).toEuclideanLin
        (formalRawFrameGram K Co z).toEuclideanLin) := by
  rw [formalRawFrameSylvester_det_iff_matrix_injective, matrix_pencil_injective_iff]

end Matrix

section Isometry
variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [FiniteDimensional ℂ F']

theorem nativePencilSylvester_isometry_intertwining
    (U : E ≃ₗᵢ[ℂ] E') (V : F ≃ₗᵢ[ℂ] F')
    (He Ge : E' →ₗ[ℂ] E') (Ho Go : F' →ₗ[ℂ] F') (W : E →ₗ[ℂ] F) :
    (U.toLinearEquiv.arrowCongr V.toLinearEquiv)
      (nativePencilSylvester
        ((LinearMap.adjoint U.toLinearMap).comp (He.comp U.toLinearMap))
        ((LinearMap.adjoint U.toLinearMap).comp (Ge.comp U.toLinearMap))
        ((LinearMap.adjoint V.toLinearMap).comp (Ho.comp V.toLinearMap))
        ((LinearMap.adjoint V.toLinearMap).comp (Go.comp V.toLinearMap)) W) =
      nativePencilSylvester He Ge Ho Go
        ((U.toLinearEquiv.arrowCongr V.toLinearEquiv) W) := by
  rw [U.adjoint_toLinearMap_eq_symm, V.adjoint_toLinearMap_eq_symm]
  ext x
  simp [nativePencilSylvester]

theorem nativePencilSylvester_isometry_injective_iff
    (U : E ≃ₗᵢ[ℂ] E') (V : F ≃ₗᵢ[ℂ] F')
    (He Ge : E' →ₗ[ℂ] E') (Ho Go : F' →ₗ[ℂ] F') :
    Function.Injective (nativePencilSylvester
        ((LinearMap.adjoint U.toLinearMap).comp (He.comp U.toLinearMap))
        ((LinearMap.adjoint U.toLinearMap).comp (Ge.comp U.toLinearMap))
        ((LinearMap.adjoint V.toLinearMap).comp (Ho.comp V.toLinearMap))
        ((LinearMap.adjoint V.toLinearMap).comp (Go.comp V.toLinearMap))) ↔
      Function.Injective (nativePencilSylvester He Ge Ho Go) := by
  let e : (E →ₗ[ℂ] F) ≃ₗ[ℂ] (E' →ₗ[ℂ] F') :=
    U.toLinearEquiv.arrowCongr V.toLinearEquiv
  constructor
  · intro hi A B hab
    obtain ⟨a,rfl⟩ := e.surjective A
    obtain ⟨b,rfl⟩ := e.surjective B
    apply congrArg e
    apply hi
    apply e.injective
    simpa only [e, nativePencilSylvester_isometry_intertwining] using hab
  · intro hi A B hab
    apply e.injective
    apply hi
    simpa only [e, nativePencilSylvester_isometry_intertwining] using congrArg e hab

end Isometry
end Zeta23.OPICARound4.NativeParitySeparation
