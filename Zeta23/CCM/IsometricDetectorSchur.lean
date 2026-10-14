import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-!
Exact Schur completion for an isometric predecessor embedding. The
complement has arbitrary finite dimension, and the predecessor may be
zero-dimensional. The inverse acts on the actual compressed predecessor
block; this file does not assume a one-dimensional detector complement.
-/

def isometricDetectorComplement (J : E →ₗᵢ[ℂ] F) : Submodule ℂ F :=
  (LinearMap.range J.toLinearMap)ᗮ

/-- The actual orthogonal complement coordinate, defined directly by
subtracting the embedded adjoint coordinate. -/
def isometricDetectorComplementCoordinate (J : E →ₗᵢ[ℂ] F) :
    F →ₗ[ℂ] isometricDetectorComplement J :=
  (LinearMap.id - J.toLinearMap.comp J.toLinearMap.adjoint).codRestrict _ (by
    intro p
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro u hu
    obtain ⟨v, hv⟩ := hu
    change J v = u at hv
    rw [← hv]
    change inner ℂ (p - J (J.toLinearMap.adjoint p)) (J v) = 0
    rw [inner_sub_left, ← LinearMap.adjoint_inner_left J.toLinearMap v p,
      J.inner_map_map, sub_self])

theorem coe_isometricDetectorComplementCoordinate (J : E →ₗᵢ[ℂ] F) (p : F) :
    (isometricDetectorComplementCoordinate J p : F) = p - J (J.toLinearMap.adjoint p) := rfl

theorem isometricDetector_coordinate_decomposition (J : E →ₗᵢ[ℂ] F) (p : F) :
    J (J.toLinearMap.adjoint p) + (isometricDetectorComplementCoordinate J p : F) = p := by
  rw [coe_isometricDetectorComplementCoordinate]
  abel

theorem inner_isometricDetectorComplementCoordinate (J : E →ₗᵢ[ℂ] F)
    (z : F) (y : isometricDetectorComplement J) :
    inner ℂ (isometricDetectorComplementCoordinate J z) y = inner ℂ z (y : F) := by
  change inner ℂ (z - J (J.toLinearMap.adjoint z)) (y : F) = inner ℂ z (y : F)
  have horth : inner ℂ (J (J.toLinearMap.adjoint z)) (y : F) = 0 :=
    (Submodule.mem_orthogonal _ _).mp y.property _ ⟨J.toLinearMap.adjoint z, rfl⟩
  rw [inner_sub_left, horth, sub_zero]

theorem isometricDetectorComplement_adjoint_eq_zero (J : E →ₗᵢ[ℂ] F)
    (y : isometricDetectorComplement J) : J.toLinearMap.adjoint (y : F) = 0 := by
  apply ext_inner_right ℂ
  intro v
  rw [LinearMap.adjoint_inner_left, inner_zero_left]
  exact (Submodule.mem_orthogonal' _ _).mp y.property _ ⟨v, rfl⟩

def isometricDetectorCoupling (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) :
    isometricDetectorComplement J →ₗ[ℂ] E :=
  J.toLinearMap.adjoint.comp (T.comp (isometricDetectorComplement J).subtype)

def isometricDetectorResponse (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (Ti : E ≃ₗ[ℂ] E) :
    isometricDetectorComplement J →ₗ[ℂ] E :=
  Ti.symm.toLinearMap.comp (isometricDetectorCoupling J T)

/-- The actual complementary Schur operator: project T(y-JP⁻¹By)
back into the whole orthogonal complement. -/
def isometricDetectorSchurOperator (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F) (Ti : E ≃ₗ[ℂ] E) :
    isometricDetectorComplement J →ₗ[ℂ] isometricDetectorComplement J :=
  (isometricDetectorComplementCoordinate J).comp
    (T.comp ((isometricDetectorComplement J).subtype -
      J.toLinearMap.comp (isometricDetectorResponse J T Ti)))

theorem inner_isometricDetectorSchurOperator (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (Ti : E ≃ₗ[ℂ] E) (y : isometricDetectorComplement J) :
    inner ℂ (isometricDetectorSchurOperator J T Ti y) y =
      inner ℂ (T ((y : F) - J (isometricDetectorResponse J T Ti y))) (y : F) := by
  exact inner_isometricDetectorComplementCoordinate J _ y

/-- Exact complex completion of squares, before taking a real part. -/
theorem isometricDetectorSchur_completedSquare (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (Ti : E ≃ₗ[ℂ] E)
    (hTi : ∀ v, Ti v = J.toLinearMap.adjoint (T (J v))) (p : F) :
    let x := J.toLinearMap.adjoint p
    let y := isometricDetectorComplementCoordinate J p
    let z := x + isometricDetectorResponse J T Ti y
    inner ℂ (T p) p = inner ℂ (Ti z) z + inner ℂ (isometricDetectorSchurOperator J T Ti y) y := by
  let x := J.toLinearMap.adjoint p
  let y := isometricDetectorComplementCoordinate J p
  let r := isometricDetectorResponse J T Ti y
  let z := x + r
  let q : F := (y : F) - J r
  have hrec : J x + (y : F) = p := isometricDetector_coordinate_decomposition J p
  have hp : p = J z + q := by
    rw [← hrec]
    dsimp only [z, q]
    rw [map_add]
    abel
  have hres : J.toLinearMap.adjoint (T q) = 0 := by
    dsimp only [q]
    rw [map_sub, map_sub, ← hTi]
    change J.toLinearMap.adjoint (T (y : F)) -
      Ti (Ti.symm (J.toLinearMap.adjoint (T (y : F)))) = 0
    rw [Ti.apply_symm_apply, sub_self]
  have hcross (v : E) : inner ℂ (T q) (J v) = 0 := by
    rw [← LinearMap.adjoint_inner_left J.toLinearMap v (T q), hres, inner_zero_left]
  have hcross' : inner ℂ (T (J z)) q = 0 := by
    rw [hT (J z) q, ← LinearMap.adjoint_inner_right J.toLinearMap z (T q), hres, inner_zero_right]
  have hpred : inner ℂ (T (J z)) (J z) = inner ℂ (Ti z) z := by
    rw [← LinearMap.adjoint_inner_left J.toLinearMap z (T (J z)), ← hTi]
  have hy : (y : F) = q + J r := by dsimp only [q]; abel
  have hschur : inner ℂ (isometricDetectorSchurOperator J T Ti y) y = inner ℂ (T q) q := by
    rw [inner_isometricDetectorSchurOperator]
    change inner ℂ (T q) (y : F) = inner ℂ (T q) q
    rw [hy, inner_add_right, hcross r, add_zero]
  change inner ℂ (T p) p = inner ℂ (Ti z) z + inner ℂ (isometricDetectorSchurOperator J T Ti y) y
  rw [hp]
  simp only [map_add, inner_add_left, inner_add_right, hpred, hcross z, hcross',
    hschur, add_zero, zero_add]

/-- The original deep detector forces negative energy on its actual
complement; no overlap with a separately selected ground is used. -/
theorem isometricDetectorSchur_negative_depth (J : E →ₗᵢ[ℂ] F) (T : F →ₗ[ℂ] F)
    (hT : T.IsSymmetric) (Ti : E ≃ₗ[ℂ] E)
    (hTi : ∀ v, Ti v = J.toLinearMap.adjoint (T (J v)))
    (hpositive : ∀ v, 0 ≤ (inner ℂ (Ti v) v).re)
    (D eta : ℝ) (hD : 0 < D) (heta : eta < D / 2) (p : F)
    (hp : (inner ℂ (T p) p).re ≤ -(D - eta)) :
    let y := isometricDetectorComplementCoordinate J p
    y ≠ 0 ∧ (inner ℂ (isometricDetectorSchurOperator J T Ti y) y).re ≤ -(D - eta) ∧
      (inner ℂ (isometricDetectorSchurOperator J T Ti y) y).re < -D / 2 := by
  let x := J.toLinearMap.adjoint p
  let y := isometricDetectorComplementCoordinate J p
  let z := x + isometricDetectorResponse J T Ti y
  have heq := congrArg Complex.re (isometricDetectorSchur_completedSquare J T hT Ti hTi p)
  change (inner ℂ (T p) p).re =
    (inner ℂ (Ti z) z + inner ℂ (isometricDetectorSchurOperator J T Ti y) y).re at heq
  rw [Complex.add_re] at heq
  have hpos := hpositive z
  have hdepth : (inner ℂ (isometricDetectorSchurOperator J T Ti y) y).re ≤ -(D - eta) := by
    linarith
  have hstrict : (inner ℂ (isometricDetectorSchurOperator J T Ti y) y).re < -D / 2 := by
    linarith
  refine ⟨?_, hdepth, hstrict⟩
  intro hy
  rw [hy, map_zero, inner_zero_left, Complex.zero_re] at hstrict
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.isometricDetector_coordinate_decomposition
#print axioms Zeta23.CCM.isometricDetectorComplement_adjoint_eq_zero
#print axioms Zeta23.CCM.inner_isometricDetectorSchurOperator
#print axioms Zeta23.CCM.isometricDetectorSchur_completedSquare
#print axioms Zeta23.CCM.isometricDetectorSchur_negative_depth
